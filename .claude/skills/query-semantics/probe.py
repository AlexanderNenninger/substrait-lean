"""Run one query through every frontend and backend sverify uses, next to the
Lean model's own result. The fallback of the `query-semantics` skill, for when
the repository's static sources don't settle a question.

Frontends (query -> Substrait):
  datafusion   DataFusion's SQL producer (SQL strings)
  ibis         sverify's vendored Ibis producer (`--ibis`)
  isthmus      Isthmus, where this checkout has it and finds the binary
Each plan goes through `substrait-check`: verified (with Lean's `Rel` and
`Rel.eval` rows on the given tables) or the parser's refusal.

Backends, on Lean's written plan (`substrait-check --write`): duckdb, polars,
datafusion, spark (`--spark`, needs a JVM); Snowflake as generated SQL only.
Native: the original query on DataFusion, DuckDB, Polars SQL and Spark SQL
(and an `--ibis` expression on Ibis's DuckDB, Polars and DataFusion backends),
which is what each engine itself makes of it.

Every row set is compared with Lean's (in order if the plan's order matters,
else as bags; doubles to six decimals, times as microseconds, dates as days).

Run from python/:
  uv run python ../.claude/skills/query-semantics/probe.py \\
      --table n 'x:int64,s:string' '[(1, "a"), (None, None)]' \\
      --sql 'SELECT x, x IN (1, NULL) AS i FROM n'
  ... --ibis 't.select("x", i=t.x.isin([1, None]))'   (t is the first table)
  ... --catalogue win-top-n-per-group                 (its synthetic tables)
"""

from __future__ import annotations

import argparse
import ast
import datetime as dt
import json
import math
import re
import sys
import warnings
from decimal import Decimal
from typing import Any

import ibis
import pyarrow as pa

import sverify.engine as eng
from sverify.sql import Unsupported, parse_plan
from sverify.sql import to_sql as plan_sql
from sverify.sql.core import Emit, Fetch, Filter, OrderBy, Project, Window, kinds
from sverify.testing import inline_tables, lean_values

EPOCH = dt.datetime(1970, 1, 1)
Rows = list[tuple]


def short(e: BaseException | str) -> str:
    text = [ln for ln in str(e).strip().splitlines() if ln.strip()]
    msg = next((ln for ln in text if ln.startswith("error:")), text[0] if text else repr(e))
    if isinstance(e, BaseException) and type(e).__name__ not in msg:
        msg = f"{type(e).__name__}: {msg}"
    return re.sub(r"\s+", " ", msg)[:160]


#: Run-time errors the Lean model marks (`SubstraitLean/Safety.lean`): its
#: value is NULL there, and the engines running Lean's plan raise by design.
RUNTIME = re.compile(r"zero|overflow|DivideByZero|DivisionByZero|out of range", re.IGNORECASE)


def failed(e: BaseException) -> str:
    msg = short(e)
    if RUNTIME.search(msg):
        return f"raises (a run-time error the model marks; Lean's value is NULL): {msg}"
    return f"error: {msg}"


# ---------------------------------------------------------------- values


def norm(v: Any) -> Any:
    """One representation per value, the Lean model's where it has one."""
    if v is None:
        return None
    if isinstance(v, bool):
        return v
    if isinstance(v, Decimal):
        v = int(v) if v == v.to_integral_value() else float(v)
    if isinstance(v, float):
        if math.isnan(v):
            return "NaN"
        if math.isinf(v):
            return "inf" if v > 0 else "-inf"
        r = round(v, 6)
        return int(r) if r == int(r) and abs(r) < 2**53 else r
    if isinstance(v, dt.datetime):
        return (v.replace(tzinfo=None) - EPOCH) // dt.timedelta(microseconds=1)
    if isinstance(v, dt.date):
        return (v - EPOCH.date()).days
    if isinstance(v, dt.timedelta):
        return v // dt.timedelta(microseconds=1)
    if hasattr(v, "months") and hasattr(v, "nanoseconds"):  # pa.MonthDayNano
        return f"interval({v.months}m {v.days}d {v.nanoseconds}ns)"
    return v


def positional(t: pa.Table) -> Rows:
    # Positional: `SELECT *` over a join may repeat column names.
    return [
        tuple(norm(v) for v in r) for r in zip(*(c.to_pylist() for c in t.columns), strict=True)
    ]


def same(a: Rows, b: Rows, ordered: bool) -> bool:
    if ordered:
        return [repr(r) for r in a] == [repr(r) for r in b]
    return sorted(map(repr, a)) == sorted(map(repr, b))


def promises_order(r: Any) -> bool:
    """Does the query promise a row order (a sort that reaches the result)?"""
    while isinstance(r, (Emit, Project, Filter)):
        r = r.input
    return isinstance(r, OrderBy) or (isinstance(r, Fetch) and promises_order(r.input))


def has_ties(r: Any) -> bool:
    """A window or FETCH: rows tied on the sort keys may come out in any order,
    so their row numbers, neighbours or selection differ legitimately."""
    if isinstance(r, (Window, Fetch)):
        return True
    return any(has_ties(getattr(r, k)) for k in ("input", "left", "right") if hasattr(r, k))


def show(rows: Rows, limit: int = 6) -> str:
    text = ", ".join(repr(r) for r in rows[:limit])
    return f"[{text}{', …' if len(rows) > limit else ''}] ({len(rows)} rows)"


# ---------------------------------------------------------------- inputs


def cell(v: Any, t: pa.DataType) -> Any:
    """A row value as given on the command line: timestamps and dates may be
    ISO strings, doubles "nan", "inf" or "-inf"."""
    if isinstance(v, str):
        if pa.types.is_timestamp(t):
            return dt.datetime.fromisoformat(v)
        if pa.types.is_date(t):
            return dt.date.fromisoformat(v)
        if pa.types.is_floating(t):
            return float(v)
    return v


def tables_from_args(specs: list[list[str]]) -> dict[str, pa.Table]:
    out = {}
    for name, cols, rows in specs:
        schema = ibis.schema(dict(c.split(":", 1) for c in cols.split(","))).to_pyarrow()
        data = [
            {f.name: cell(v, f.type) for f, v in zip(schema, r, strict=True)}
            for r in ast.literal_eval(rows)
        ]
        out[name] = pa.Table.from_pylist(data, schema=schema)
    return out


def catalogue_query(qid: str) -> tuple[dict[str, pa.Table], str | None, str | None]:
    from sverify import catalogue as cat

    schemas = cat.load_schemas()
    q = next(q for q in cat.load_queries() if q.id == qid)
    tables = cat.synthetic(schemas, q.dataset, "native")
    return tables, q.sql, q.ibis


# ---------------------------------------------------------------- frontends


def frontends(con: eng.Connection, sql: str | None, expr: Any) -> dict[str, tuple[str, str]]:
    """name -> (plan JSON or "", outcome)."""
    out: dict[str, tuple[str, str]] = {}
    if sql is not None:
        try:
            out["datafusion"] = (eng.substrait_json(con, sql), "plan")
        except Exception as e:  # noqa: BLE001
            out["datafusion"] = ("", f"no plan: {short(e)}")
        isthmus = getattr(eng, "isthmus_json", None)
        if isthmus is not None and eng.isthmus_path() is not None:
            try:
                out["isthmus"] = (isthmus(con, sql), "plan")
            except Exception as e:  # noqa: BLE001
                out["isthmus"] = ("", f"no plan: {short(e)}")
        elif isthmus is None:
            out["isthmus"] = ("", "not in this checkout (PR #92)")
        else:
            out["isthmus"] = ("", "no binary ($SVERIFY_ISTHMUS or isthmus on PATH)")
    if expr is not None:
        from sverify.ibis_substrait import to_substrait_json

        try:
            out["ibis"] = (to_substrait_json(expr), "plan")
        except Exception as e:  # noqa: BLE001
            out["ibis"] = ("", f"refused: {short(e)}")
    return out


def lean(plan: str, tables: dict[str, pa.Table]) -> tuple[str, str, Rows | None]:
    """(checker verdict, Lean's Rel, Rel.eval rows on `tables`)."""
    code, out, err = eng.run_checker((), plan)
    if code != 0:
        return f"rejected: {short(out + err)}", "", None
    rel = out.split("\ntables:")[0]
    flags = [ln for ln in out.splitlines() if ln.startswith(("incremental:", "deterministic"))]
    rows = {n: [tuple(r.values()) for r in t.to_pylist()] for n, t in tables.items()}
    try:
        inlined = json.dumps(inline_tables(json.loads(eng.written_plan(plan)), rows))
        got = lean_values(inlined)
        ks = kinds(parse_plan(json.loads(eng.written_plan(plan))).root)
        lean_rows = [
            tuple(
                norm(v) if k != "float" or v is None else norm(float(v))
                for v, k in zip(r, ks, strict=True)
            )
            for r in got
        ]
    except Exception as e:  # noqa: BLE001
        return f"verified ({'; '.join(flags)}); no Rel.eval: {short(e)}", rel, None
    return "verified (" + "; ".join(flags) + ")", rel, lean_rows


# ---------------------------------------------------------------- backends


def backends(
    con: eng.Connection, written: str, tables: dict[str, pa.Table], spark: bool
) -> dict[str, tuple[str, Rows | None]]:
    from sverify import polars_engine
    from sverify.sql.snowflake import SNOWFLAKE

    out: dict[str, tuple[str, Rows | None]] = {}
    for engine in eng.ENGINES:
        try:
            out[engine] = ("ran", positional(eng.run_plan(con, written, engine)))
        except (Unsupported, polars_engine.Unsupported) as e:
            out[engine] = (f"refused: {short(e)}", None)
        except Exception as e:  # noqa: BLE001
            out[engine] = (failed(e), None)
    if spark:
        try:
            from sverify import spark_engine

            out["spark"] = ("ran", positional(spark_engine.run(written, tables)))
        except Unsupported as e:
            out["spark"] = (f"refused: {short(e)}", None)
        except Exception as e:  # noqa: BLE001
            out["spark"] = (failed(e), None)
    try:
        text = plan_sql(json.loads(written), SNOWFLAKE)
        out["snowflake"] = ("SQL generated (not run): " + " ".join(text.split())[:200], None)
    except Unsupported as e:
        out["snowflake"] = (f"refused: {short(e)}", None)
    return out


def native_sql(con: eng.Connection, sql: str, tables: dict[str, pa.Table], spark: bool):
    import duckdb
    import polars as pl

    out: dict[str, tuple[str, Rows | None]] = {}

    def attempt(name: str, f) -> None:
        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                out[name] = ("ran", positional(f()))
        except Exception as e:  # noqa: BLE001
            out[name] = (f"error: {short(e)}", None)

    attempt("datafusion", lambda: con.datafusion.sql(sql).to_arrow_table())
    db = duckdb.connect()
    for n, t in tables.items():
        db.register(n, t)
    attempt("duckdb", lambda: db.sql(sql).fetch_arrow_table())
    ctx = pl.SQLContext({n: pl.from_arrow(t) for n, t in tables.items()})
    attempt("polars", lambda: ctx.execute(sql, eager=True).to_arrow())
    if spark:
        from sverify import spark_engine

        def run_spark():
            spark_engine.put_tables(tables)
            return spark_engine.session().sql(sql).toArrow()

        attempt("spark", run_spark)
    return out


def ibis_expr(code: str, tables: dict[str, Any]) -> Any:
    """The expression `code` builds over Ibis tables `tables` (`t` is the
    first): an expression, or statements that assign `q`."""
    ns = {"ibis": ibis, "_": ibis._, **tables, "t": next(iter(tables.values()))}
    try:
        return eval(code, ns)  # noqa: S307 - the user's own expression
    except SyntaxError:
        exec(code, ns)  # noqa: S102
        return ns["q"]


def native_ibis(code: str, tables: dict[str, pa.Table]):
    # Memtables: `create_table` of an Arrow table fails on Ibis's DuckDB
    # backend with the pinned versions.
    expr = ibis_expr(code, {n: ibis.memtable(t) for n, t in tables.items()})
    out: dict[str, tuple[str, Rows | None]] = {}
    for name in ("duckdb", "polars", "datafusion"):
        try:
            out[name] = ("ran", positional(getattr(ibis, name).connect().to_pyarrow(expr)))
        except Exception as e:  # noqa: BLE001
            out[name] = (f"error: {short(e)}", None)
    return out


# ---------------------------------------------------------------- main


def verdict(status: str, rows: Rows | None, model: Rows | None, ordered: bool) -> str:
    if rows is None:
        return status
    if model is None:
        return f"{status}: {show(rows)}"
    mark = "= Lean" if same(rows, model, ordered) else "DIFFERS from Lean"
    return f"{mark}: {show(rows)}"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--table", nargs=3, action="append", default=[],
                    metavar=("NAME", "COL:TYPE,...", "ROWS"))  # fmt: skip
    ap.add_argument("--sql")
    ap.add_argument("--ibis", help="Ibis code: an expression, or statements assigning q")
    ap.add_argument("--catalogue", help="a catalogue query id: its query and synthetic tables")
    ap.add_argument("--spark", action="store_true", help="also run on Spark (needs a JVM)")
    args = ap.parse_args()

    tables = tables_from_args(args.table)
    sql, code = args.sql, args.ibis
    if args.catalogue:
        tables, cat_sql, cat_ibis = catalogue_query(args.catalogue)
        sql, code = sql or cat_sql, code or cat_ibis
    if not tables or (sql is None and code is None):
        ap.error("give --table(s) and --sql and/or --ibis, or --catalogue")

    con = eng.connect()
    for n, t in tables.items():
        con.put(n, t)
    expr = None
    if code is not None:
        expr = ibis_expr(code, {n: con.table(n) for n in tables})
        if sql is None:
            print("Ibis's DataFusion SQL:", " ".join(eng.to_sql(expr).split())[:300])

    model: Rows | None = None
    ordered = False
    print("== Frontends (query -> Substrait -> substrait-check)")
    plans = frontends(con, sql, expr)
    first_verified: str | None = None
    for name, (plan, outcome) in plans.items():
        if not plan:
            print(f"  {name:11} {outcome}")
            continue
        status, rel, rows = lean(plan, tables)
        print(f"  {name:11} {status}")
        if rel:
            print("    " + rel.replace("\n", "\n    "))
        if rows is not None:
            print(f"    Rel.eval: {show(rows)}")
            if model is None:
                model, first_verified = rows, plan
                root = parse_plan(json.loads(eng.written_plan(plan))).root
                ordered = promises_order(root)
                if has_ties(root):
                    print("    note: a window or FETCH: where sort keys tie, engines may number,")
                    print(
                        "    pair or pick rows differently from Rel.eval's stable order and still"
                    )
                    print("    be right (pitfall tie_order; notebook 14, O2, O3, O5).")
            elif not same(rows, model, ordered):
                print("    (differs from the first verified frontend's Rel.eval)")
    if first_verified is not None:
        name = next(n for n, (p, _) in plans.items() if p == first_verified)
        print(f"\n== Backends on Lean's written plan (from {name}; "
              f"compared {'in order' if ordered else 'as bags'})")  # fmt: skip
        for engine, (status, rows) in backends(con, eng.written_plan(first_verified), tables,
                                               args.spark).items():  # fmt: skip
            print(f"  {engine:11} {verdict(status, rows, model, ordered)}")
    else:
        print("\n== No frontend's plan verified: nothing runs Lean's semantics")
    if sql is not None:
        print("\n== Native: the SQL itself on each engine")
        for engine, (status, rows) in native_sql(con, sql, tables, args.spark).items():
            print(f"  {engine:11} {verdict(status, rows, model, ordered)}")
    if code is not None:
        print("\n== Native: the Ibis expression on Ibis's backends")
        for engine, (status, rows) in native_ibis(code, tables).items():
            print(f"  {engine:11} {verdict(status, rows, model, ordered)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

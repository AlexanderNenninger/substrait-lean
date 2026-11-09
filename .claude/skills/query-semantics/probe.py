"""Run one query through every frontend, profile and engine sverify uses,
next to the reference's own result (`Rel.eval`). The fallback of the
`query-semantics` skill, for when the static sources (`lookup.py`) don't
settle a question.

Frontends (query -> Substrait):
  lift         sverify's SQLGlot lift of DuckDB's SQL (SQL strings)
  ibis         sverify's vendored Ibis producer (`--ibis`)
Each plan goes through `substrait-check`: verified (with Lean's `Rel` and
`Rel.eval` rows on the given tables) or the parser's refusal.

Profiles: `sv.verify` under the reference, DuckDB's, Polars's (Ibis only)
and Substrait's (once #600 lands), with the route and class
(`sverify.routes.choose`) to each engine.

Engines, on the written plan (`substrait-check --write`): DuckDB and Polars
(the profiles; Polars on its streaming engine), DataFusion and Spark
(`--spark`, needs a JVM) outside the profiles (#271); Snowflake as generated
SQL only. Native: the original query on DuckDB, Polars SQL, DataFusion and
Spark SQL (and an `--ibis` expression on Ibis's DuckDB, Polars and DataFusion
backends), which is what each engine itself makes of it.

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
from sverify_polars import engine as polars_engine
from sverify.sql import Unsupported, parse_plan
from sverify.sql import to_sql as plan_sql
from sverify.sql.core import Emit, Fetch, Filter, OrderBy, Project, Window, kinds
from sverify.testing import inline_tables, lean_values

sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent))
import lookup  # noqa: E402

EPOCH = dt.datetime(1970, 1, 1)
#: The engines with a profile; the others run outside the profiles (#271).
PROFILED = ("duckdb", "polars")
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


# ---------------------------------------------------------- environment


def polars_streaming() -> str:
    """Make sverify's Polars runs use the streaming engine, as #605 does,
    and say how they run. sverify's own flags stay (predicate pushdown off)."""
    import polars as pl

    if hasattr(polars_engine, "collect_streaming"):
        return "streaming (sverify's collect, #605)"

    def collect(lf: pl.LazyFrame) -> pl.DataFrame:
        return lf.collect(
            engine="streaming", optimizations=pl.QueryOptFlags(predicate_pushdown=False)
        )

    polars_engine.collect = collect
    return "streaming (patched in by the probe until #605 lands; predicate pushdown off)"


def native_polars(lf: Any) -> Any:
    """A native Polars query: the streaming engine, Polars's default
    optimizations."""
    return lf.collect(engine="streaming")


def environment(con: eng.Connection, spark: bool, polars_mode: str) -> None:
    """The engine versions, the profiles' versions and the settings the
    profiles' facts depend on (D14; #598's settings check)."""
    import importlib.metadata as md

    from sverify import routes

    print("== Environment")
    pkgs = ["sverify", "duckdb", "polars", "datafusion", "ibis-framework", "sqlglot"]
    if spark:
        pkgs.append("pyspark")
    vers = []
    for p in pkgs:
        try:
            vers.append(f"{p} {md.version(p)}")
        except md.PackageNotFoundError:
            vers.append(f"{p} (not installed)")
    print("  " + ", ".join(vers))
    for name, prof in routes.profiles().items():
        installed = routes.installed_version(prof.engine)
        try:
            note = routes.check_version(prof.engine) or "matches"
        except Exception as err:  # noqa: BLE001
            note = f"REFUSED: {err}"
        print(
            f"  Profile.{name}: facts probed at {', '.join(prof.versions)}; "
            f"installed {installed}: {note}"
        )
    print(f"  polars: {polars_mode}")
    try:
        from sverify import _engine_settings as es  # #598

        for engine in PROFILED:
            cur = es.current(engine)
            print(f"  {engine} settings: " + ", ".join(f"{k}={v}" for k, v in cur.items()))
            for msg in es.check_settings(engine):
                print(f"    differs from the profile: {msg}")
    except ImportError:
        import duckdb

        names = [
            "default_null_order",
            "default_order",
            "integer_division",
            "error_on_division_by_zero",
            "ieee_floating_point_ops",
            "default_collation",
            "preserve_insertion_order",
            "threads",
            "TimeZone",
        ]
        db = duckdb.connect()
        got = []
        for n in names:
            try:
                got.append(f"{n}={db.sql(f"SELECT current_setting('{n}')").fetchall()[0][0]}")
            except Exception:  # noqa: BLE001 - not a setting in this version
                continue
        print("  duckdb settings (a fresh connection; #598 adds the check): " + ", ".join(got))
        import os

        aff = os.environ.get("POLARS_ENGINE_AFFINITY", "auto")
        print(f"  polars engine affinity: {aff} (sverify names engine='streaming' anyway)")


def few_rows(tables: dict[str, pa.Table]) -> list[str]:
    return [n for n, t in tables.items() if t.num_rows < 2]


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
    from sverify_dev import catalogue as cat

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
            out["lift"] = (eng.substrait_json(con, sql), "plan")
        except Exception as e:  # noqa: BLE001
            out["lift"] = ("", f"no plan: {short(e)}")
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
    from sverify_polars import engine as polars_engine
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
            from sverify_spark import engine as spark_engine

            out["spark"] = ("ran", positional(spark_engine.run(written, tables)))
        except Unsupported as e:
            out["spark"] = (f"refused: {short(e)}", None)
        except Exception as e:  # noqa: BLE001
            out["spark"] = (failed(e), None)
    try:
        text = plan_sql(json.loads(written), SNOWFLAKE)
        out["snowflake"] = (
            "SQL generated, not run, outside the profiles: " + " ".join(text.split())[:100] + " …",
            None,
        )
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

    db = duckdb.connect()
    for n, t in tables.items():
        db.register(n, t)
    attempt("duckdb", lambda: db.sql(sql).fetch_arrow_table())
    ctx = pl.SQLContext({n: pl.from_arrow(t).lazy() for n, t in tables.items()})
    attempt("polars", lambda: native_polars(ctx.execute(sql)).to_arrow())
    attempt("datafusion", lambda: con.datafusion.sql(sql).to_arrow_table())
    if spark:
        from sverify_spark import engine as spark_engine

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
            backend = getattr(ibis, name).connect()
            if name == "polars":
                got = native_polars(backend.compile(expr)).to_arrow()
            else:
                got = backend.to_pyarrow(expr)
            out[name] = ("ran", positional(got))
        except Exception as e:  # noqa: BLE001
            out[name] = (f"error: {short(e)}", None)
    return out


# ---------------------------------------------------------------- main


def verdict(status: str, rows: Rows | None, model: Rows | None, ordered: bool) -> str:
    if rows is None:
        return status
    if model is None:
        return f"{status}: {show(rows)}"
    mark = "= Rel.eval" if same(rows, model, ordered) else "DIFFERS from Rel.eval"
    return f"{mark}: {show(rows)}"


def route_of(report: Any, engine: str) -> str:
    """The route and class to `engine`, short, or why there is none."""
    if engine not in PROFILED:
        return "outside the profiles (#271): the writer's shims, tested only"
    if report is None:
        return "no verified report: no route"
    from sverify import routes

    try:
        r = routes.choose(report, engine)
    except Exception as err:  # noqa: BLE001
        return f"{type(err).__name__}: {short(err)}"
    if r.refused:
        return f"refused: {r.reason[:140]}"
    out = f"{r.kind} from Profile.{report.semantics} [{r.cls or 'no class until #587'}]"
    return out + (f"; shims: {'; '.join(r.shims)}" if r.shims else "")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument(
        "--table", nargs=3, action="append", default=[], metavar=("NAME", "COL:TYPE,...", "ROWS")
    )
    ap.add_argument("--sql", help="the query, in DuckDB's SQL")
    ap.add_argument("--ibis", help="Ibis code: an expression, or statements assigning q")
    ap.add_argument(
        "--requires",
        nargs=2,
        action="append",
        default=[],
        metavar=("TABLE", "EXPR"),
        help="a precondition: an Ibis expression over _, or sv.max_rows(n)",
    )
    ap.add_argument(
        "--ensures",
        action="append",
        default=[],
        metavar="EXPR",
        help="a postcondition, e.g. sv.equivalent(floats=sv.within(rel=1e-9))",
    )
    ap.add_argument("--catalogue", help="a catalogue query id: its query and synthetic tables")
    ap.add_argument(
        "--spark", action="store_true", help="also run on Spark (needs a JVM; outside the profiles)"
    )
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
    environment(con, args.spark, polars_streaming())
    if small := few_rows(tables):
        print(f"  note: {', '.join(small)} has fewer than 2 rows. Polars rewrites arithmetic with")
        print(
            "  literals differently on one-row frames (PL-3, polars-zero-sign): give 2 rows"
            " or more."
        )
    expr = None
    if code is not None:
        expr = ibis_expr(code, {n: con.table(n) for n in tables})
        if sql is None:
            print("Ibis's DuckDB SQL:", " ".join(ibis.to_sql(expr, dialect="duckdb").split())[:300])

    model: Rows | None = None
    ordered = False
    print("\n== Frontends (query -> Substrait -> substrait-check, the reference)")
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
                    print("    be right (option tie_order; the observation 'ties permuted').")
            elif not same(rows, model, ordered):
                print("    (differs from the first verified frontend's Rel.eval)")

    schemas = {n: ibis.Schema.from_pyarrow(t.schema) for n, t in tables.items()}
    req, ens = lookup.conditions(args.requires, args.ensures)
    reports = lookup.verify_profiles(expr if expr is not None else sql, schemas, req, ens)
    lookup.print_profiles(reports)
    verified = [r for r in reports.values() if not isinstance(r, str) and r.proved]
    best = verified[0] if verified else None

    if first_verified is not None:
        name = next(n for n, (p, _) in plans.items() if p == first_verified)
        print(
            f"\n== Engines on the written plan (from {name}; "
            f"compared {'in order' if ordered else 'as bags'}; route from Profile."
            f"{best.semantics if best else '-'})"
        )
        for engine, (status, rows) in backends(
            con, eng.written_plan(first_verified), tables, args.spark
        ).items():
            print(f"  {engine:11} {verdict(status, rows, model, ordered)}")
            if engine != "snowflake":
                print(f"  {'':11}   route: {route_of(best, engine)}")
    else:
        print("\n== No frontend's plan verified under the reference: Rel.eval gives no rows")
    if sql is not None:
        print("\n== Native: the SQL itself on each engine (no route; what the engine does)")
        for engine, (status, rows) in native_sql(con, sql, tables, args.spark).items():
            print(f"  {engine:11} {verdict(status, rows, model, ordered)}")
    if code is not None:
        print("\n== Native: the Ibis expression on Ibis's backends")
        for engine, (status, rows) in native_ibis(code, tables).items():
            print(f"  {engine:11} {verdict(status, rows, model, ordered)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

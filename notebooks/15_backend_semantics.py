# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "duckdb",
#     "ibis-framework[datafusion,duckdb,polars]==12.0.0",
#     "marimo",
#     "polars",
#     "sverify",
# ]
#
# [tool.uv.sources]
# sverify = { path = "../python", editable = true }
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="full", app_title="15. One expression, many engines")


@app.cell(hide_code=True)
def _():
    import marimo as mo

    return (mo,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 14. [DataFusion's surprising semantics](?file=14_datafusion_semantics.py) · [Contents](?file=00_start_here.py)
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 15. One expression, many engines

    A query or an Ibis expression has no single meaning: each engine gives it
    its own. This notebook collects the questions that a semantics written
    *from first principles* (instead of read off one implementation) has to
    answer, and shows how each engine answers them today. It is the companion
    of [chapter 14](?file=14_datafusion_semantics.py), which compares
    DataFusion alone with the Lean model.

    Every entry is one small question, such as "what is `-7 % 2`?" or "where do
    NULLs go in a descending sort?". It is asked three ways, and every answer
    except Snowflake's is computed live when the notebook runs:

    * **Native engines.** The SQL runs on **DataFusion** and **DuckDB**, and
      the Polars expression runs on **Polars**. **Snowflake** is quoted from
      its documentation, since there is no account to run on. The SQL standard
      is given in prose where it says something.
    * **Ibis.** One Ibis expression, executed by Ibis's **DataFusion**,
      **DuckDB** and **Polars** backends. The Snowflake SQL that Ibis
      compiles it to is under "Snowflake SQL". Ibis promises one meaning for
      one expression, and this column tests that promise.
    * **Lean and sverify.** `Rel.eval` of the plan that DataFusion makes from
      the SQL (Lean prints doubles with a `d`, ±0.0 as their codes ±1, and
      timestamps as microseconds). Then the plan Lean writes back out
      (`written_plan`), run by sverify's own translators to **Polars** and
      **DuckDB**, plus whether the **Snowflake** and **Spark** SQL generators
      accept it (chapter 11 runs the Spark SQL on a real Spark session).
      These translators are meant to reproduce `Rel.eval` exactly, whatever
      the native engine would do.

    Each entry gets three tags:

    * **engines**: `uniform` if the native engines agree, `split` if they
      don't. A `split` entry is a decision a formal semantics must make
      explicitly.
    * **Ibis**: `portable` if the Ibis expression gives the same result on
      every backend, `leaky` if the backend shows through. This tag is
      computed live (comparing results as bags) and is blank when no Ibis
      backend runs the expression.
    * **sverify**: `faithful` if both translators give Lean's answer (or fail
      where Lean says a runtime error is possible), `refused` if the checker
      or a translator rejects the plan, `opaque` if Lean leaves the function
      uninterpreted and the translators disagree, and `GAP` if a translator
      is wrong.

    sverify verifies an Ibis expression by compiling it to DataFusion's SQL,
    so the meaning sverify checks is the one **Ibis-on-DataFusion** gives it.
    Wherever the Ibis tag is `leaky`, running the same expression on another
    Ibis backend can break what was proved.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Summary

    Built from the catalogue below. First, the entries where sverify itself
    is wrong or undetermined, then the Ibis expressions whose meaning depends
    on the backend, and last the questions the engines answer differently,
    each with the answer the Lean model gives today.
    """)
    return


@app.cell(hide_code=True)
def _(catalogue, mo, render):
    _bad = [e for e in catalogue if e.sverify in ("GAP", "opaque")]
    _leaky = [e for e in catalogue if e.out["ibis_tag"] == "leaky"]
    _split = [e for e in catalogue if e.engines == "split"]

    def _choices(es):
        rows = "".join(
            "<tr style='border-top:1px solid #8883'>"
            f"<td style='padding:3px 12px 3px 0;opacity:.6'>{e.id}</td>"
            f"<td style='padding:3px 12px 3px 0'>{e.title}</td>"
            f"<td style='padding:3px 12px 3px 0'>{e.picks}</td></tr>"
            for e in es
        )
        return mo.Html(
            "<table style='border-collapse:collapse;font-size:0.85rem;width:auto;margin:0'>"
            "<thead><tr><th></th><th style='text-align:left'>question</th>"
            "<th style='text-align:left'>the Lean model's answer today</th></tr></thead>"
            f"<tbody>{rows}</tbody></table>"
        )

    mo.vstack(
        [
            mo.md(
                f"**{len(catalogue)} questions**: {len(_split)} split the engines, "
                f"{len(_leaky)} Ibis expressions are leaky, and sverify has "
                f"{sum(e.sverify == 'GAP' for e in catalogue)} gaps and "
                f"{sum(e.sverify == 'opaque' for e in catalogue)} opaque functions."
            ),
            mo.md("### sverify gaps and opaque functions"),
            render(_bad),
            mo.md("### Leaky Ibis expressions"),
            mo.md(", ".join(f"**{e.id}** {e.title}" for e in _leaky)),
            mo.md("### Decisions for a formal semantics"),
            _choices(_split),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Setup

    One tiny table per topic, put into DataFusion (through `sverify`), DuckDB
    and Polars, and given to Ibis as a memtable. Lean gets the same rows,
    inlined into the plan as a Substrait virtual table. DataFusion gets the
    tables as they are (`put_table` would store them the model's way, with
    one zero and one NaN), so its native answers show its own order.
    """)
    return


@app.cell
def _():
    import datetime as dt

    import pyarrow as pa

    def ints(**cols):
        return pa.table({k: pa.array(v, pa.int64()) for k, v in cols.items()})

    I64_MAX = 2**63 - 1
    tables = {
        "n": ints(x=[1, None, 2]),
        "j": ints(a=[1, None]),
        "k": ints(g=[1, 1, 2, None], v=[None, None, 3, 4]),
        "e": ints(x=[]),
        "dm": ints(a=[-7, 7, -7], b=[2, -2, -2]),
        "z": ints(a=[1, 0], b=[0, 0]),
        "mx": ints(a=[I64_MAX, -I64_MAX - 1]),
        "sm": ints(a=[I64_MAX, 1]),
        "big": ints(a=[2**53 + 1]),
        "r": pa.table({"v": [2.5, -2.5, 0.5, 1.5, 2.7]}),
        "f": pa.table({"v": [float("nan"), 0.0, 1.0, None, float("-inf")]}),
        "f0": pa.table({"v": [-0.0, 0.0]}),
        "s": pa.table({"s": ["hello", "é", "🎉", "", None]}),
        "ss": pa.table({"s": ["Straße", "a\\b"]}),
        "u": pa.table({"s": ["٣", "3", "a b"]}),
        "ts": pa.table(
            {
                "t": pa.array(
                    [dt.datetime(2024, 1, 7), dt.datetime(2024, 1, 31), dt.datetime(2021, 1, 3)],
                    pa.timestamp("us"),
                )
            }
        ),
        "w": ints(g=[1, 1, 1, 2], o=[1, 2, 2, 1], v=[10, 20, 30, 40]),
    }
    return dt, tables


@app.cell(hide_code=True)
def _(dt, pa, tables):
    import json
    import re
    import warnings
    from dataclasses import dataclass, field

    import duckdb
    import ibis
    import polars as pl
    import sverify as sv
    from sverify import duckdb_engine, polars_engine
    from sverify.engine import read_tables, run_checker, substrait_json, written_plan
    from sverify.incremental import arrow_rows
    from sverify.sql import Unsupported
    from sverify.sql import to_sql as plan_sql
    from sverify.sql.snowflake import SNOWFLAKE
    from sverify.sql.spark import SPARK
    from sverify.testing import inline_tables

    con = sv.connect()
    duck = duckdb.connect()
    for _name, _t in tables.items():
        _batches = _t.to_batches() or [pa.RecordBatch.from_pylist([], schema=_t.schema)]
        con.con.register_record_batches(_name, [_batches])
        duck.register(_name, _t)
    P = {k: pl.from_arrow(t) for k, t in tables.items()}
    MEM = {k: ibis.memtable(t) for k, t in tables.items()}
    IBIS = {b: getattr(ibis, b).connect() for b in ("datafusion", "duckdb", "polars")}

    def positional(t) -> list[tuple]:
        """Rows by position: SQL allows two output columns with one name."""
        return list(zip(*[c.to_pylist() for c in t.columns], strict=True))

    def show(v: object) -> str:
        if v is None:
            return "NULL"
        if isinstance(v, dt.datetime):
            return v.isoformat(sep=" ")
        return repr(v)

    def fmt(rows: list[tuple]) -> str:
        if not rows:
            return "(no rows)"
        if all(len(r) == 1 for r in rows):
            text = ", ".join(show(r[0]) for r in rows)
        else:
            text = ", ".join("(" + ", ".join(map(show, r)) + ")" for r in rows)
        return text if len(text) < 140 else text[:137] + "…"

    def short_error(e: Exception) -> str:
        msg = str(e).replace("DataFusion error: ", "").strip().splitlines()[0]
        return f"error ({type(e).__name__}): " + (msg if len(msg) < 90 else msg[:87] + "…")

    def attempt(f, bag: bool = False) -> tuple[str, object]:
        """The result as text, and a value to compare (the rows, or their bag
        when `bag`) or the error's class."""
        try:
            rows = f()
        except Exception as e:
            return short_error(e), ("error", type(e).__name__)
        values = list(map(repr, rows))
        return fmt(rows), sorted(values) if bag else values

    def lean_rows(plan: str) -> str:
        """`Rel.eval` of the plan on the same rows, as `substrait-check` prints it."""
        rows = {n: arrow_rows(tables[n]) for n in read_tables(json.loads(plan))}
        inlined = inline_tables(json.loads(plan), rows)
        _, out, _ = run_checker((), json.dumps(inlined))
        got = [ln.strip() for ln in out.split("rows (")[1].splitlines()[1:] if ln.startswith("  (")]
        text = ", ".join(r[1:-1] if "," not in r else r for r in got) or "(no rows)"
        return text if len(text) < 140 else text[:137] + "…"

    def generated(plan: str, dialect) -> str:
        try:
            plan_sql(json.loads(plan), dialect)
        except Unsupported as e:
            return "refused: " + str(e).split(" (")[0][:90]
        return "SQL generated"

    @dataclass
    class E:
        id: str
        title: str
        on: str
        sql: str
        why: str
        picks: str
        ibis: str | None = None
        polars: str | None = None
        snowflake: str = ""
        std: str = ""
        duck: str | None = "same"
        engines: str = "uniform"
        sverify: str = "faithful"
        unordered: bool = False
        out: dict = field(default_factory=dict)

        def run(self) -> "E":
            o = self.out
            o["df"] = attempt(lambda: positional(con.con.sql(self.sql).to_arrow_table()))[0]
            duck_sql = self.sql if self.duck == "same" else self.duck
            o["duck"] = attempt(lambda: duck.sql(duck_sql).fetchall())[0] if duck_sql else None
            with warnings.catch_warnings():
                # Polars warns about `== None` (N1), which is the point of N1.
                warnings.simplefilter("ignore")
                o["polars"] = (
                    attempt(lambda: eval(self.polars, {"pl": pl, "t": P[self.on]}).rows())[0]
                    if self.polars
                    else None
                )
            o["ibis"], o["ibis_sf"], o["ibis_tag"] = {}, "", ""
            if self.ibis:
                expr = eval(self.ibis, {"ibis": ibis, "t": MEM[self.on]})
                bags = {}
                for b, c in IBIS.items():
                    o["ibis"][b], bags[b] = attempt(
                        lambda c=c: positional(c.to_pyarrow(expr)), self.unordered
                    )
                ran = [v for v in bags.values() if v[:1] != ("error",)]
                undefined = {"OperationNotDefinedError", "TypeError"}
                errors = {v[1] for v in bags.values() if v[:1] == ("error",)} - undefined
                o["ibis_tag"] = (
                    ""
                    if not ran and not errors
                    else "portable"
                    if (all(v == ran[0] for v in ran) and not (ran and errors))
                    else "leaky"
                )
                try:
                    sf = ibis.to_sql(expr, dialect="snowflake")
                    o["ibis_sf"] = re.sub(
                        r'"ibis_pyarrow_memtable_\w+"', self.on, " ".join(sf.split())
                    )
                except Exception as e:
                    o["ibis_sf"] = short_error(e)
            try:
                plan = substrait_json(con, self.sql)
            except Exception as e:
                o["lean"], o["sv"], self.sverify = "no plan: " + short_error(e), [], "refused"
                return self
            code, out, err = run_checker((), plan)
            if code:
                o["lean"] = (
                    "refused: " + (err or out).strip().splitlines()[-1].removeprefix("error: ")[:90]
                )
                o["sv"], self.sverify = [], "refused"
                return self
            wp = written_plan(plan)
            tabs = {n: tables[n] for n in read_tables(json.loads(wp))}
            o["lean"] = lean_rows(plan)
            (pt, pv), (dt_, dv) = (
                attempt(lambda run=run: positional(run(wp, tabs)), self.unordered)
                for run in (polars_engine.run, duckdb_engine.run)
            )
            o["sv"] = [("Polars", pt), ("DuckDB", dt_)]
            o["sql"] = [("Snowflake", generated(wp, SNOWFLAKE)), ("Spark", generated(wp, SPARK))]
            # The translators agree when both fail or both give the same rows.
            o["sv_agree"] = pv == dv or (pv[:1] == dv[:1] == ("error",))
            return self

    return E, pl


@app.cell(hide_code=True)
def _(mo):
    import html

    COLORS = {
        "uniform": "#2e8b57",
        "split": "#b8860b",
        "portable": "#2e8b57",
        "leaky": "#c0392b",
        "faithful": "#2e8b57",
        "refused": "#2f6db5",
        "opaque": "#b8860b",
        "GAP": "#c0392b",
    }

    def _tag(label: str, value: str) -> str:
        if not value:
            return ""
        return f"{label} <b style='color:{COLORS[value]}'>{value}</b>"

    def _lines(pairs) -> str:
        """`name: value` lines; one line when all values are equal."""
        pairs = [(k, v) for k, v in pairs if v is not None]
        if len(pairs) > 1 and len({v for _, v in pairs}) == 1:
            return f"<i>all {len(pairs)}</i>: {html.escape(pairs[0][1])}"
        return "<br>".join(f"<i>{k}</i>: {html.escape(v)}" for k, v in pairs)

    def render(es):
        """A compact table: one row per question."""
        cell = "text-align:left;vertical-align:top;padding:4px 12px 4px 0"
        mono = "font-family:var(--monospace-font, monospace);font-size:0.78rem"
        cols = ["", "question", "query", "native engines", "Ibis", "Lean · sverify", "verdict"]
        head = "".join(f"<th style='{cell}'>{c}</th>" for c in cols)
        body = []
        for e in es:
            o = e.out
            query = html.escape(e.sql)
            if e.ibis:
                query += f"<br><span style='opacity:.7'>ibis: {html.escape(e.ibis)}</span>"
            if e.polars:
                query += f"<br><span style='opacity:.7'>polars: {html.escape(e.polars)}</span>"
            native = []
            if e.std:
                native.append(f"<i>SQL standard</i>: {html.escape(e.std)}")
            native.append(
                _lines([("DataFusion", o["df"]), ("DuckDB", o["duck"]), ("Polars", o["polars"])])
            )
            if e.snowflake:
                native.append(f"<i>Snowflake (docs)</i>: {html.escape(e.snowflake)}")
            ib = _lines(list(o["ibis"].items())) if o["ibis"] else "—"
            if o["ibis_sf"]:
                ib += (
                    "<details><summary style='opacity:.7'>Snowflake SQL</summary>"
                    f"<span style='{mono}'>{html.escape(o['ibis_sf'])}</span></details>"
                )
            lean = f"<i>Lean</i>: {html.escape(o['lean'])}"
            if o["sv"]:
                lean += "<br>" + _lines([(f"sverify→{k}", v) for k, v in o["sv"]])
                lean += "<br>" + _lines([(f"sverify→{k}", v) for k, v in o["sql"]])
                if not o["sv_agree"]:
                    lean += "<br><b>the two translators disagree</b>"
            tags = " · ".join(
                t
                for t in (
                    _tag("engines", e.engines),
                    _tag("Ibis", o["ibis_tag"]),
                    _tag("sverify", e.sverify),
                )
                if t
            )
            body.append(
                "<tr style='border-top:1px solid #8883'>"
                f"<td style='{cell};opacity:.6'>{e.id}</td>"
                f"<td style='{cell};min-width:8rem'>{html.escape(e.title)}</td>"
                f"<td style='{cell};{mono};max-width:20rem'>{query}</td>"
                f"<td style='{cell};{mono};max-width:20rem'>{'<br>'.join(native)}</td>"
                f"<td style='{cell};{mono};max-width:17rem'>{ib}</td>"
                f"<td style='{cell};{mono};max-width:17rem'>{lean}</td>"
                f"<td style='{cell};font-size:0.85rem;max-width:22rem'>{tags}<br>"
                f"{html.escape(e.why)}<br><i>Lean</i>: {html.escape(e.picks)}</td>"
                "</tr>"
            )
        return mo.Html(
            "<table style='border-collapse:collapse;font-size:0.85rem;width:auto;margin:0'>"
            f"<thead><tr>{head}</tr></thead><tbody>{''.join(body)}</tbody></table>"
        )

    return (render,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 1. NULL and three-valued logic

    SQL has three truth values: TRUE, FALSE and UNKNOWN (written NULL). A
    comparison with NULL is UNKNOWN, and a filter keeps a row only when its
    condition is TRUE. `AND` and `OR` follow Kleene's tables: `FALSE AND NULL`
    is FALSE, but `TRUE AND NULL` is NULL. Every engine agrees on that core.
    The differences are in what the *surface* languages, Ibis and Polars,
    choose to mean by `==`, `isin` and friends.
    """)
    return


@app.cell(hide_code=True)
def _(E, render):
    nulls = [
        E(
            "N1",
            "comparing with a NULL literal",
            "n",
            "SELECT x, x = NULL FROM n",
            ibis="t.select('x', q=t.x == ibis.null())",
            polars="t.select('x', q=pl.col('x') == None)",
            std="UNKNOWN for every row",
            snowflake="NULL for every row",
            why="Ibis rewrites `== ibis.null()` into `IS NULL`, so in Ibis `x == NULL` is "
            "TRUE for the NULL row, on every backend. SQL and Polars' own `== None` say "
            "NULL. Portable, but an Ibis expression and the SQL it looks like mean "
            "different things.",
            picks="NULL (SQL), since sverify reads the SQL Ibis emits",
        ).run(),
        E(
            "N2",
            "IN / NOT IN with a NULL in the list",
            "n",
            "SELECT x, x IN (1, NULL), x NOT IN (2, NULL) FROM n",
            ibis="t.select('x', i=t.x.isin([1, None]), ni=t.x.notin([2, None]))",
            polars="t.select('x', i=pl.col('x').is_in([1, None]), "
            "ni=~pl.col('x').is_in([2, None]))",
            std="x IN (…, NULL) is TRUE or NULL, never FALSE",
            snowflake="standard",
            engines="split",
            why="`x NOT IN (2, NULL)` can never be TRUE, the classic SQL trap. "
            "Polars' `is_in` ignores the NULL and says FALSE/TRUE. Ibis-on-Polars "
            "corrects for it.",
            picks="SQL's three-valued answer",
        ).run(),
        E(
            "N3",
            "Kleene AND / OR",
            "n",
            "SELECT x, x > 1 OR NULL, x > 1 AND NULL FROM n",
            ibis="t.select('x', o=(t.x > 1) | ibis.null(bool), a=(t.x > 1) & ibis.null(bool))",
            polars="t.select('x', o=(pl.col('x') > 1) | pl.lit(None, pl.Boolean), "
            "a=(pl.col('x') > 1) & pl.lit(None, pl.Boolean))",
            std="Kleene: FALSE AND NULL = FALSE, TRUE OR NULL = TRUE",
            snowflake="Kleene",
            why="Everyone implements Kleene logic.",
            picks="Kleene (`and3`, `or3`)",
        ).run(),
        E(
            "N4",
            "join on a NULL key",
            "j",
            "SELECT a.a, b.a FROM j a JOIN j b ON a.a = b.a",
            ibis="t.join(t.view(), 'a')",
            polars="t.join(t, on='a')",
            std="NULL = NULL is UNKNOWN, so NULL keys never match",
            snowflake="standard",
            why="Every engine drops the NULL key. The query's two output columns are both "
            "called `a`, legal in SQL and in Substrait's `RelRoot.names` but not in a "
            "Polars frame. sverify's Polars translator used to crash on it; it now names "
            "the Arrow result instead.",
            picks="NULL keys never match",
        ).run(),
        E(
            "N5",
            "IS [NOT] DISTINCT FROM",
            "j",
            "SELECT a, a IS DISTINCT FROM NULL, a IS NOT DISTINCT FROM 1 FROM j",
            ibis="t.select('a', d=t.a.identical_to(ibis.null('int64')), n=t.a.identical_to(1))",
            polars="t.select('a', n=pl.col('a').eq_missing(1))",
            std="NULL-safe equality: never NULL",
            snowflake="supported, standard",
            why="The NULL-safe comparison everyone has, with different names. Ibis's "
            "`identical_to` is `IS NOT DISTINCT FROM`, so `d` is the negation of the SQL "
            "column.",
            picks="two-valued, NULL equals NULL",
        ).run(),
        E(
            "N6",
            "string concatenation with NULL",
            "s",
            "SELECT s, s || 'x', concat(s, 'x') FROM s",
            ibis="t.select('s', c=t.s + 'x', d=t.s.concat('x'))",
            polars="t.select('s', c=pl.col('s') + 'x', d=pl.concat_str([pl.col('s'), pl.lit('x')]))",
            std="`||` with NULL is NULL",
            snowflake="`||` and CONCAT are NULL if any argument is",
            engines="split",
            why="DataFusion's and DuckDB's `concat()` skip NULL arguments (as "
            "PostgreSQL's does); `||` propagates. Ibis's `concat` propagates on every "
            "backend. Lean has `||` only and refuses `concat`.",
            picks="refuses concat(); `||` propagates NULL",
        ).run(),
    ]
    render(nulls)
    return (nulls,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 2. Order: NULL placement, row numbers and window frames

    A table is a *bag* of rows: it has no order until `ORDER BY` gives it one,
    and even then rows with equal keys (ties) may come out in any order. Where
    NULLs go in a sort is a convention. The SQL standard leaves it to the
    implementation, but it must be consistent: NULLs sort either above or
    below every value. Window functions add *frames*: which rows a running
    `SUM` adds up. The standard's default frame when there is an `ORDER BY` is
    `RANGE BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW`, and `RANGE` means
    rows tied with the current one (its *peers*) are included.
    """)
    return


@app.cell(hide_code=True)
def _(E, render):
    order = [
        E(
            "O1",
            "NULLs in an ascending sort",
            "n",
            "SELECT x FROM n ORDER BY x",
            ibis="t.order_by('x')",
            polars="t.sort('x')",
            std="implementation-defined, but NULLs are all above or all below the values",
            snowflake="NULLS LAST (DEFAULT_NULL_ORDERING = LAST)",
            engines="split",
            sverify="faithful",
            why="Polars puts NULLs first by default, the SQL engines last. Ibis asks "
            "for NULLs last on every backend. The translators follow the plan's explicit "
            "NULLS LAST. sverify's Snowflake SQL refuses sorts and windows over a named "
            "table (Snowflake tables have no row order to break ties by), here and in "
            "O2–O5.",
            picks="as the plan says (DataFusion writes NULLS LAST)",
        ).run(),
        E(
            "O2",
            "NULLs in a descending sort",
            "n",
            "SELECT x FROM n ORDER BY x DESC",
            ibis="t.order_by(ibis.desc('x'))",
            polars="t.sort('x', descending=True)",
            std="the mirror of ascending, if NULLs are 'largest'",
            snowflake="NULLS FIRST (NULLs are largest)",
            engines="split",
            sverify="faithful",
            why="DataFusion and Snowflake treat NULL as the largest value, so it comes "
            "first in DESC. DuckDB puts NULLs last in both directions. Ibis always "
            "says NULLs last, which is not the mirror of SQL's default. So one Ibis "
            "expression and its SQL look-alike sort differently.",
            picks="as the plan says (DataFusion writes NULLS FIRST)",
        ).run(),
        E(
            "O3",
            "row numbers start at …",
            "w",
            "SELECT g, v, row_number() OVER (ORDER BY g, v) FROM w",
            ibis="t.select('g', 'v', r=ibis.row_number().over(order_by=['g', 'v']))",
            polars="t.with_row_index('r').select('g', 'v', 'r')",
            std="ROW_NUMBER() starts at 1",
            snowflake="1",
            engines="split",
            sverify="faithful",
            why="Ibis's `row_number()` is 0-based (it compiles to `ROW_NUMBER() - 1`), "
            "and so is Polars' row index. SQL's starts at 1. Ibis-on-Polars has no "
            "window functions.",
            picks="1-based (SQL)",
        ).run(),
        E(
            "O4",
            "running SUM: the default frame",
            "w",
            "SELECT g, o, v, sum(v) OVER (PARTITION BY g ORDER BY o) FROM w ORDER BY g, o, v",
            ibis="t.select('g', 'o', 'v', s=t.v.sum().over(group_by='g', order_by='o'))"
            ".order_by(['g', 'o', 'v'])",
            polars="t.with_columns(s=pl.col('v').cum_sum().over('g', order_by='o'))"
            ".sort(['g', 'o', 'v'])",
            std="RANGE UNBOUNDED PRECEDING .. CURRENT ROW: ties (peers) included",
            snowflake="RANGE UNBOUNDED PRECEDING .. CURRENT ROW",
            engines="split",
            sverify="refused",
            why="Three answers. SQL includes the peers (20 and 30 tie on o = 2, so both get "
            "60). Polars' `cum_sum` counts rows (30, then 60). Ibis's default frame is the "
            "whole partition even with an `order_by` (every row of g = 1 gets 60), and it "
            "writes `ROWS BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED FOLLOWING` into the "
            "SQL. Lean refuses `sum` as a window function.",
            picks="refused",
        ).run(),
        E(
            "O5",
            "LAG at the start of a partition",
            "w",
            "SELECT g, o, v, lag(v) OVER (PARTITION BY g ORDER BY o, v) FROM w ORDER BY g, o, v",
            ibis="t.select('g', 'o', 'v', l=t.v.lag().over(group_by='g', order_by=['o', 'v']))"
            ".order_by(['g', 'o', 'v'])",
            polars="t.with_columns(l=pl.col('v').shift(1).over('g', order_by=['o', 'v']))"
            ".sort(['g', 'o', 'v'])",
            std="NULL (or the default argument)",
            snowflake="NULL (or the default argument)",
            why="Uniform once the order is total. With ties in the window's ORDER BY, "
            "which row is 'previous' depends on the engine. Lean breaks ties by input "
            "order (a stable sort).",
            picks="NULL; ties broken by input order",
        ).run(),
    ]
    render(order)
    return (order,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 3. Integers

    Mathematical integers are unbounded, while engines store them in 64 bits
    (`BIGINT`, values from −2⁶³ to 2⁶³ − 1). The questions are what `/` and
    `%` mean on integers, what happens at the edges (division by zero,
    overflow), and what a cast does. "Truncating" division rounds toward
    zero (−7 / 2 = −3); "floor" division rounds down (−7 // 2 = −4). The
    remainder follows: truncating gives −7 % 2 = −1, floor gives +1.
    """)
    return


@app.cell(hide_code=True)
def _(E, render):
    integers = [
        E(
            "I1",
            "integer / integer",
            "dm",
            "SELECT a / b FROM dm",
            ibis="t.select(q=t.a / t.b)",
            polars="t.select(q=pl.col('a') / pl.col('b'))",
            std="an exact numeric of implementation-defined scale; truncation in practice",
            snowflake="a decimal rounded to 6 places (-3.500000)",
            engines="split",
            why="DataFusion truncates to an integer; DuckDB, Polars and Ibis "
            "always give a double. Snowflake gives a decimal. Ibis's `/` is true division "
            "on every backend. Translated, DuckDB and Polars truncate as Lean does.",
            picks="truncating (`Int.tdiv`), as DataFusion",
        ).run(),
        E(
            "I2",
            "the sign of a remainder",
            "dm",
            "SELECT a % b FROM dm",
            ibis="t.select(q=t.a % t.b)",
            polars="t.select(q=pl.col('a') % pl.col('b'))",
            std="MOD: the sign of the dividend",
            snowflake="the sign of the dividend",
            engines="split",
            why="Polars' `%` is Python's: floor, so the sign of the divisor. Ibis passes "
            "that through, so Ibis's `%` gives −1 on DataFusion and DuckDB but +1 on "
            "Polars.",
            picks="truncating (`Int.tmod`)",
        ).run(),
        E(
            "I3",
            "floor division //",
            "dm",
            "SELECT a // b FROM dm",
            ibis="t.select(q=t.a // t.b)",
            polars="t.select(q=pl.col('a') // pl.col('b'))",
            snowflake="no operator; Ibis writes FLOOR(a / b), over a 6-place decimal",
            engines="split",
            why="DataFusion's SQL has no `//`. DuckDB's `//` is not what its name "
            "suggests: it truncates (−3) on integers. Polars and Ibis floor (−4); sverify "
            "has a shim so Ibis's `//` reaches DataFusion as a floor. On Snowflake, Ibis's "
            "`FLOOR(a / b)` rounds the quotient to 6 decimals first, so it can be off by one "
            "for large operands.",
            picks="no `//` in SQL; Ibis's floor reaches Lean through the shim",
        ).run(),
        E(
            "I4",
            "integer division by zero",
            "z",
            "SELECT a / b FROM z",
            ibis="t.select(q=t.a // t.b)",
            polars="t.select(q=pl.col('a') // pl.col('b'))",
            std="an exception (data exception: division by zero)",
            snowflake="error: Division by zero (DIV0 gives 0, DIV0NULL gives NULL)",
            engines="split",
            why="DataFusion raises. DuckDB's `/` is double division, so 1/0 = inf and "
            "0/0 = NaN. Polars gives NULL. Through Ibis that is an error on DataFusion and "
            "DuckDB (casting inf to an integer) and NULL on Polars. Lean's value is NULL "
            "and `Safety.lean` reports `divByZero`; the translators raise.",
            picks="NULL plus a runtime issue that must be proved absent",
        ).run(),
        E(
            "I5",
            "remainder by zero",
            "z",
            "SELECT a % b FROM z",
            ibis="t.select(q=t.a % t.b)",
            polars="t.select(q=pl.col('a') % pl.col('b'))",
            std="an exception",
            snowflake="error",
            engines="split",
            why="Polars gives NULL; the SQL engines raise.",
            picks="NULL plus `divByZero`",
        ).run(),
        E(
            "I6",
            "64-bit overflow on +",
            "mx",
            "SELECT a + 1 FROM mx WHERE a > 0",
            ibis="t.filter(t.a > 0).select(q=t.a + 1)",
            polars="t.filter(pl.col('a') > 0).select(q=pl.col('a') + 1)",
            std="an exception (numeric value out of range)",
            snowflake="no overflow: NUMBER(38,0) holds 2⁶³",
            engines="split",
            why="DataFusion and Polars wrap around to −2⁶³ silently; DuckDB raises; "
            "Snowflake's integers are 38-digit decimals and do not overflow here. Lean's "
            "integers are unbounded (it prints 2⁶³ as a double code, a known rendering "
            "bug) and the checker warns `wraps`; the translators raise.",
            picks="unbounded, plus a `wraps` warning",
        ).run(),
        E(
            "I7",
            "negating the smallest integer",
            "mx",
            "SELECT -a FROM mx WHERE a < 0",
            ibis="t.filter(t.a < 0).select(q=-t.a)",
            polars="t.filter(pl.col('a') < 0).select(q=-pl.col('a'))",
            std="an exception",
            snowflake="no overflow",
            engines="split",
            why="As I6: −(−2⁶³) does not fit in 64 bits.",
            picks="unbounded, plus `wraps`",
        ).run(),
        E(
            "I8",
            "SUM overflow",
            "sm",
            "SELECT sum(a) FROM sm",
            ibis="t.aggregate(s=t.a.sum())",
            polars="t.select(pl.col('a').sum())",
            std="an exception",
            snowflake="exact (38 digits)",
            engines="split",
            sverify="faithful",
            why="DuckDB sums BIGINT into a 128-bit HUGEINT and gets 2⁶³ exactly, which "
            "Ibis then cannot convert back to int64. DataFusion and Polars wrap. The "
            "translators raise, since Lean's exact sum leaves 64 bits.",
            picks="unbounded (the `sum` of `Rel.eval` is exact)",
        ).run(),
        E(
            "I9",
            "AVG of large integers",
            "mx",
            "SELECT avg(a) FROM mx",
            ibis="t.aggregate(m=t.a.mean())",
            polars="t.select(pl.col('a').mean())",
            std="exact numeric, implementation-defined precision",
            snowflake="exact decimal: -0.5",
            engines="split",
            sverify="faithful",
            why="The true mean of 2⁶³ − 1 and −2⁶³ is −0.5. DataFusion and Polars "
            "convert each value to a double first, where both round to ±2⁶³, so they "
            "sum to 0. DuckDB sums exactly. Lean gives +0.0 (code 1), DataFusion's "
            "answer, and so do the translators.",
            picks="+0.0, DataFusion's double accumulation",
        ).run(),
        E(
            "I10",
            "a narrowing cast that does not fit",
            "sm",
            "SELECT CAST(a AS INT) AS c FROM sm",
            ibis="t.select(c=t.a.cast('int32'))",
            polars="t.select(c=pl.col('a').cast(pl.Int32, strict=False))",
            std="an exception",
            snowflake="no 32-bit type: INT is NUMBER(38,0)",
            engines="split",
            why="DataFusion and DuckDB raise; Polars' non-strict cast gives NULL. Lean "
            "used to read the cast as the identity (chapter 14, I8). It is now "
            "`UnFn.narrow`: NULL plus a `badCast` issue where the value does not fit, so "
            "`verify` reports the possible error and both translators raise.",
            picks="an error where the value does not fit (`badCast`)",
        ).run(),
    ]
    render(integers)
    return (integers,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 4. Doubles and rounding

    IEEE 754 doubles have two zeros (+0.0 and −0.0, equal under IEEE `=`) and
    NaN ("not a number", unequal to everything, itself included, under IEEE
    `=`). Databases cannot use IEEE `=` as is, because GROUP BY and DISTINCT
    need an equality where every value equals itself. So each engine picks
    its own fix, and the fixes differ. Rounding a half (2.5) also has two
    common conventions: *half away from zero* (2.5 → 3, −2.5 → −3) and *half
    to even*, also called banker's rounding (2.5 → 2, 3.5 → 4).
    """)
    return


@app.cell(hide_code=True)
def _(E, render):
    floats = [
        E(
            "F1",
            "-0.0 = 0.0",
            "f0",
            "SELECT v, v = 0.0, v < 0.0 FROM f0",
            ibis="t.select('v', a=t.v == 0.0, b=t.v < 0.0)",
            polars="t.select('v', a=pl.col('v') == 0.0, b=pl.col('v') < 0.0)",
            std="IEEE: -0.0 = 0.0",
            snowflake="not documented",
            engines="split",
            why="DataFusion compares doubles by their total order, where −0.0 < +0.0. "
            "DuckDB, Polars and Spark follow IEEE (equal), and so does the model, which "
            "has one zero: the least surprise.",
            picks="one zero: −0.0 = 0.0",
        ).run(),
        E(
            "F2",
            "DISTINCT over ±0.0",
            "f0",
            "SELECT DISTINCT v FROM f0",
            unordered=True,
            ibis="t.select('v').distinct()",
            polars="t.unique()",
            std="IEEE equality would merge them",
            snowflake="not documented",
            engines="split",
            why="It follows from F1: DataFusion keeps both zeros, DuckDB and Polars "
            "merge them, as the model does. Ibis inherits each backend's answer.",
            picks="one value, 0.0",
        ).run(),
        E(
            "F3",
            "NaN equals itself, and sorts above +∞",
            "f",
            "SELECT v, v = v, v > 1e308 FROM f",
            ibis="t.select('v', a=t.v == t.v, b=t.v > 1e308)",
            polars="t.select('v', a=pl.col('v') == pl.col('v'), b=pl.col('v') > 1e308)",
            std="IEEE: NaN = NaN is false",
            snowflake="NaN = NaN, and NaN is above +inf",
            why="Every engine here departs from IEEE in the same way: NaN equals NaN "
            "and is the largest double, so `ORDER BY` and `GROUP BY` work. Uniform, but "
            "not IEEE.",
            picks="one NaN, above +∞ (`Float.lean`)",
        ).run(),
        E(
            "F4",
            "MAX over a column with NaN",
            "f",
            "SELECT max(v), min(v) FROM f",
            ibis="t.aggregate(a=t.v.max(), b=t.v.min())",
            polars="t.select(a=pl.col('v').max(), b=pl.col('v').min())",
            snowflake="NaN (it is the largest)",
            engines="split",
            sverify="refused",
            why="Consistent with F3, the SQL engines return NaN. Polars' `max` skips "
            "NaN and returns 1.0, and so does Ibis-on-Polars. Lean refuses `max` of "
            "doubles.",
            picks="refused",
        ).run(),
        E(
            "F5",
            "double division by zero",
            "f",
            "SELECT v / 0.0 FROM f",
            ibis="t.select(q=t.v / 0.0)",
            polars="t.select(q=pl.col('v') / 0.0)",
            std="an exception",
            snowflake="error: Division by zero",
            why="Everyone that runs follows IEEE: ±inf, or NaN for 0/0 and NaN/0. "
            "Snowflake raises even on doubles.",
            picks="IEEE",
        ).run(),
        E(
            "F6",
            "CAST(2.5 AS BIGINT)",
            "r",
            "SELECT v, CAST(v AS BIGINT) AS c FROM r",
            ibis="t.select('v', c=t.v.cast('int64'))",
            polars="t.select('v', c=pl.col('v').cast(pl.Int64))",
            std="implementation-defined: truncate or round",
            snowflake="rounds ('Converting a FLOAT to INTEGER rounds the value')",
            engines="split",
            why="DataFusion and Polars truncate (2.7 → 2). DuckDB rounds half to even "
            "(2.5 → 2, 1.5 → 2, 2.7 → 3). Snowflake rounds too (the docs do not say how "
            "halves go). So Ibis's `cast('int64')` depends on the backend. The "
            "translators truncate, as Lean does.",
            picks="truncate",
        ).run(),
        E(
            "F7",
            "round(2.5)",
            "r",
            "SELECT v, round(v) FROM r",
            ibis="t.select('v', r=t.v.round())",
            polars="t.select('v', r=pl.col('v').round())",
            snowflake="half away from zero (ROUND's default rounding_mode)",
            engines="split",
            why="The SQL engines round half away from zero (2.5 → 3, 0.5 → 1); Polars "
            "rounds half to even (2.5 → 2, 0.5 → 0). Ibis's `round()` returns an integer "
            "and inherits each convention.",
            picks="half away from zero",
        ).run(),
        E(
            "F8",
            "integers above 2⁵³ as doubles",
            "big",
            "SELECT a, CAST(a AS DOUBLE) = CAST(a - 1 AS DOUBLE) FROM big",
            ibis="t.select('a', q=t.a.cast('float64') == (t.a - 1).cast('float64'))",
            polars="t.select('a', q=pl.col('a').cast(pl.Float64) == "
            "(pl.col('a') - 1).cast(pl.Float64))",
            std="approximate: the nearest double",
            snowflake="the nearest double",
            why="A double has 53 bits of mantissa, so 2⁵³ + 1 and 2⁵³ become the same "
            "double. Uniform: round to nearest, ties to even.",
            picks="IEEE round-to-nearest (`Float.ofInt`)",
        ).run(),
        E(
            "F9",
            "CAST(2.7 AS BIGINT) of a constant",
            "j",
            "SELECT CAST(2.7 AS BIGINT) AS c FROM j",
            ibis="t.select(c=ibis.literal(2.7).cast('int64'))",
            polars="t.select(c=pl.lit(2.7).cast(pl.Int64))",
            std="implementation-defined: truncate or round",
            snowflake="rounds",
            engines="split",
            why="DataFusion truncates constants as it truncates columns (F6): 2. DuckDB "
            "rounds the decimal 2.7 to 3. Lean's parser folds a constant cast itself "
            "(`Const.toInt?`); it used to round, so `verify` proved `c = 3`. It now "
            "truncates, as for a column.",
            picks="truncate, for constants as for columns",
        ).run(),
    ]
    render(floats)
    return (floats,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 5. Strings

    A string is a sequence of something: bytes (UTF-8), Unicode code points,
    or grapheme clusters (what a reader sees as one character). `'é'` can be
    one code point or two; `'🎉'` is one code point and four bytes. SQL counts
    positions from 1; Python, and so Ibis and Polars, count from 0. Case
    mapping and regular expressions bring in Unicode tables, which differ
    between libraries.
    """)
    return


@app.cell(hide_code=True)
def _(E, render):
    strings = [
        E(
            "S1",
            "length: characters or bytes?",
            "s",
            "SELECT s, length(s) FROM s",
            ibis="t.select('s', l=t.s.length())",
            polars="t.select('s', l=pl.col('s').str.len_chars())",
            std="CHAR_LENGTH counts characters, OCTET_LENGTH bytes",
            snowflake="characters",
            why="Uniform in SQL: code points. But Ibis's `length()` on Polars counts "
            "bytes (`str.len_bytes`), so 'é' has length 2 there.",
            picks="code points (`Text.lean`)",
        ).run(),
        E(
            "S2",
            "SUBSTR from 0, and from −1",
            "s",
            "SELECT s, substr(s, 0, 2), substr(s, -1, 3) FROM s",
            duck="SELECT s, substr(s, 0, 2), substr(s, -1, 3) FROM s",
            ibis="t.select('s', a=t.s.substr(0, 2))",
            polars="t.select('s', a=pl.col('s').str.slice(0, 2), b=pl.col('s').str.slice(-1, 3))",
            std="positions 0 and −1 lie before the string, so they take fewer characters",
            snowflake="start 0 is read as 1 ('he'); a negative start counts from the end",
            engines="split",
            why="In SQL, `substr('hello', 0, 2)` covers positions 0 and 1, so it is 'h'. "
            "DuckDB agrees there, but counts a negative start from the end ('o'), as "
            "Snowflake and Polars do. Ibis's `substr` is 0-based, so `substr(0, 2)` "
            "is 'he' everywhere. sverify's SQL generators normalise the start first.",
            picks="the standard: positions before 1 are empty (`Text.substr`)",
        ).run(),
        E(
            "S3",
            "position of a substring",
            "s",
            "SELECT s, strpos(s, 'l') FROM s",
            ibis="t.select('s', p=t.s.find('l'))",
            polars="t.select('s', p=pl.col('s').str.find('l'))",
            std="POSITION: 1-based, 0 if absent",
            snowflake="POSITION: 1-based, 0 if absent",
            why="SQL: 1-based with 0 for 'absent'. Polars: 0-based with NULL. Ibis's "
            "`find`: 0-based with −1, but on Polars a NULL string gives −1, not NULL.",
            picks="1-based, 0 if absent",
        ).run(),
        E(
            "S4",
            "upper('ß')",
            "ss",
            "SELECT s, upper(s) FROM ss",
            ibis="t.select('s', u=t.s.upper())",
            polars="t.select('s', u=pl.col('s').str.to_uppercase())",
            snowflake="not documented",
            engines="split",
            sverify="opaque",
            why="Rust (DataFusion, Polars) maps ß to 'SS'; DuckDB's utf8proc to 'ẞ' "
            "(capital sharp s). `upper` is an uninterpreted function in Lean, so no "
            "proof depends on it. But the same verified plan gives different strings on "
            "sverify's two translators, and Lean's own evaluator only maps ASCII (it "
            "prints '' for the rest).",
            picks="uninterpreted",
        ).run(),
        E(
            "S5",
            "LIKE and the backslash",
            "ss",
            "SELECT s, s LIKE 'a\\b', s LIKE 'a\\\\b' FROM ss",
            ibis="t.select('s', a=t.s.like('a\\\\b'), b=t.s.like('a\\\\\\\\b'))",
            std="no escape character unless ESCAPE says so",
            snowflake="no default escape; a backslash in a literal is an escape itself",
            engines="split",
            why="DataFusion treats `\\` as LIKE's escape by default (as PostgreSQL does); "
            "DuckDB and the standard have none. So 'a\\b' LIKE 'a\\b' is false on DataFusion "
            "and true on DuckDB, and Ibis's `like` inherits the split. Ibis-on-Polars has "
            "no LIKE. sverify's SQL names the escape explicitly.",
            picks="backslash escapes (DataFusion)",
        ).run(),
        E(
            "S6",
            "regex classes \\d and \\s beyond ASCII",
            "u",
            "SELECT s, array_length(regexp_match(s, '\\d')), "
            "array_length(regexp_match(s, '\\s')) FROM u",
            duck="SELECT s, regexp_matches(s, '\\d'), regexp_matches(s, '\\s') FROM u",
            ibis="t.select('s', d=t.s.re_search('\\\\d'), w=t.s.re_search('\\\\s'))",
            polars="t.select('s', d=pl.col('s').str.contains('\\\\d'), "
            "w=pl.col('s').str.contains('\\\\s'))",
            snowflake="POSIX classes plus Perl's \\d, \\s, \\w; Unicode reach not documented",
            engines="split",
            sverify="opaque",
            why="Rust's regex (DataFusion, Polars) is Unicode-aware: the Arabic-Indic "
            "digit ٣ is a `\\d` and a no-break space is a `\\s`. DuckDB's RE2 is "
            "ASCII-only. Lean leaves regular expressions uninterpreted, but sverify's "
            "DuckDB and Polars translators of one verified plan disagree on ٣.",
            picks="uninterpreted",
        ).run(),
        E(
            "S7",
            "s < 'b'",
            "s",
            "SELECT s FROM s WHERE s < 'b' ORDER BY s",
            ibis="t.filter(t.s < 'b').order_by('s')",
            polars="t.filter(pl.col('s') < 'b').sort('s')",
            std="by collation; bytewise without one",
            snowflake="bytewise (UTF-8) without a collation",
            sverify="refused",
            why="Every engine compares bytewise ('' and 'S' come before 'b'). Lean's `<` "
            "has no string case, so `Rel.eval` keeps nothing; every translator refuses the "
            "plan. `verify` itself still accepts it (chapter 14, gap S6).",
            picks="NULL (wrong; see chapter 14)",
        ).run(),
        E(
            "S8",
            "casting ' 12' to an integer",
            "j",
            "SELECT CAST(' 12' AS BIGINT) AS c FROM j",
            ibis="t.select(c=ibis.literal(' 12').cast('int64'))",
            polars="t.select(c=pl.lit(' 12').cast(pl.Int64, strict=False))",
            std="leading and trailing spaces are allowed",
            engines="split",
            why="The standard and DuckDB strip the spaces; DataFusion raises; Polars' "
            "strict cast raises and its non-strict cast gives NULL. Lean folds a cast of a "
            "string constant itself. It used to trim the spaces (and accept `1_000`), so "
            "`verify` proved `c = 12` where DataFusion fails. It now reads integers, "
            "doubles, timestamps and dates as DataFusion does and refuses the rest, so "
            "the plan is refused. Casts of string columns are refused too.",
            picks="refused (DataFusion fails)",
        ).run(),
    ]
    render(strings)
    return (strings,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 6. Aggregates

    An aggregate folds a column into one value. Two conventions matter: SQL
    aggregates (except `COUNT`) skip NULLs and return NULL when nothing is
    left, and `COUNT(DISTINCT x)` does not count NULL as a value. Lean
    verifies aggregates, and sverify's translators run them with its
    semantics. Snowflake's SQL refuses a double `SUM` or `AVG` over a named
    table, whose result depends on the order rows are added in.
    """)
    return


@app.cell(hide_code=True)
def _(E, render):
    aggregates = [
        E(
            "A1",
            "aggregates of an empty table",
            "e",
            "SELECT sum(x), count(x), count(*), avg(x), min(x) FROM e",
            ibis="t.aggregate(s=t.x.sum(), c=t.x.count(), n=t.count(), m=t.x.mean(), mi=t.x.min())",
            polars="t.select(s=pl.col('x').sum(), c=pl.col('x').count(), n=pl.len(), "
            "m=pl.col('x').mean(), mi=pl.col('x').min())",
            std="SUM, AVG, MIN are NULL; COUNT is 0",
            snowflake="standard",
            engines="split",
            sverify="faithful",
            why="Polars' `sum` of nothing is 0, not NULL. Ibis-on-Polars corrects it.",
            picks="the standard",
        ).run(),
        E(
            "A2",
            "SUM of a group of NULLs",
            "k",
            "SELECT g, sum(v), count(v) FROM k GROUP BY g ORDER BY g",
            ibis="t.group_by('g').aggregate(s=t.v.sum(), c=t.v.count()).order_by('g')",
            polars="t.group_by('g').agg(s=pl.col('v').sum(), c=pl.col('v').count()).sort('g')",
            std="NULL; NULL keys form one group",
            snowflake="standard",
            engines="split",
            sverify="faithful",
            why="As A1, per group: Polars says 0 for the group of NULLs, and sorts the "
            "NULL group first. Everyone puts the NULL keys in one group.",
            picks="the standard",
        ).run(),
        E(
            "A3",
            "COUNT(DISTINCT) and NULL",
            "k",
            "SELECT count(DISTINCT v), count(DISTINCT g) FROM k",
            ibis="t.aggregate(a=t.v.nunique(), b=t.g.nunique())",
            polars="t.select(a=pl.col('v').n_unique(), b=pl.col('g').n_unique())",
            std="NULL is not counted",
            snowflake="NULL is not counted",
            engines="split",
            sverify="faithful",
            why="Polars' `n_unique` counts NULL as a value, and Ibis's `nunique` on "
            "Polars passes that through (3 instead of 2).",
            picks="the standard",
        ).run(),
    ]
    render(aggregates)
    return (aggregates,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 7. Time

    Timestamps here have no time zone and microsecond precision. The
    differences are in conventions: which day a week starts on, whether day
    numbers start at 0 or 1, and how adding a month copes with the 31st.
    """)
    return


@app.cell(hide_code=True)
def _(E, render):
    times = [
        E(
            "T1",
            "day of the week",
            "ts",
            "SELECT t, date_part('dow', t) FROM ts",
            ibis="t.select('t', d=t.t.day_of_week.index())",
            polars="t.select('t', d=pl.col('t').dt.weekday())",
            std="(EXTRACT has no day-of-week field)",
            snowflake="DAYOFWEEK depends on WEEK_START; the default 0 means Sunday = 0",
            engines="split",
            why="2024-01-07 is a Sunday. SQL's `dow` says 0 (Sunday first), Polars' "
            "`weekday` 7 (ISO: Monday = 1), Ibis's `day_of_week.index()` 6 (Monday = 0). "
            "Three conventions, and Snowflake's depends on a session parameter.",
            picks="Sunday = 0 (DataFusion)",
        ).run(),
        E(
            "T2",
            "week of the year",
            "ts",
            "SELECT t, date_part('week', t) FROM ts",
            ibis="t.select('t', w=t.t.week_of_year())",
            polars="t.select('t', w=pl.col('t').dt.week())",
            snowflake="WEEK depends on WEEK_OF_YEAR_POLICY; WEEKISO is ISO",
            why="ISO weeks everywhere: 2021-01-03 is in week 53 of 2020.",
            picks="ISO 8601 weeks",
        ).run(),
        E(
            "T3",
            "Jan 31 + 1 month",
            "ts",
            "SELECT t + INTERVAL '1 month' FROM ts",
            ibis="t.select(q=t.t + ibis.interval(months=1))",
            polars="t.select(q=pl.col('t').dt.offset_by('1mo'))",
            std="an exception (invalid date)",
            snowflake="DATEADD clamps to the last day of the month",
            sverify="refused",
            why="Every engine clamps to Feb 29; the standard would raise. Ibis-on-Polars "
            "cannot add months. Lean refuses month intervals.",
            picks="refused",
        ).run(),
        E(
            "T4",
            "truncating to the week",
            "ts",
            "SELECT date_trunc('week', t) FROM ts",
            ibis="t.select(q=t.t.truncate('W'))",
            polars="t.select(q=pl.col('t').dt.truncate('1w'))",
            snowflake="depends on WEEK_START (sverify truncates to Monday itself)",
            why="Everyone truncates to Monday.",
            picks="Monday",
        ).run(),
    ]
    render(times)
    return (times,)


@app.cell(hide_code=True)
def _(aggregates, floats, integers, nulls, order, strings, times):
    catalogue = [*nulls, *order, *integers, *floats, *strings, *aggregates, *times]
    return (catalogue,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## What this means for a formal semantics

    * **Pick, don't inherit.** Of the questions above, the `split` ones have
      no engine-neutral answer. The Lean model mostly takes DataFusion's,
      which made sense while DataFusion was the only engine. A semantics of
      its own would state each choice (truncating division, −0.0 < +0.0, NULL
      as the largest value, 1-based positions) and treat every engine as
      something to *translate into*, as sverify's Polars and DuckDB
      translators already do.
    * **Ibis is a language of its own.** Its expressions do not mean the SQL
      they compile to: `== null` is `IS NULL`, `row_number` and `find` and
      `substr` are 0-based, sorts put NULLs last in both directions, and a
      window with an `order_by` but no frame covers the whole partition. And
      where Ibis does not normalise (`%`, `round`, `cast`, `length`,
      `nunique`, `max` with NaN, `like`), the backend shows through. A
      semantics of Ibis expressions should therefore be defined on Ibis's
      own operations, with sverify checking against Ibis-on-DataFusion only
      as one implementation.
    * **Uninterpreted is not the same as agreed.** `upper`, `lower` and
      regular expressions are black boxes in Lean, which keeps proofs honest,
      but sverify's translators then compute them with different Unicode
      tables (S4, S6). Pinning them (to Rust's `str::to_uppercase` and the
      `regex` crate, say) or refusing non-ASCII input would make "the same
      plan, the same rows" true across engines.
    * **sverify gaps found here, all fixed.** Constant casts used to round
      (`CAST(2.7 AS BIGINT)` was proved to be 3; DataFusion gives 2, F9) and
      to trim spaces from strings (`' 12'` was proved to be 12; DataFusion
      fails, S8); constants now fold by the same rules as columns, and strings
      DataFusion cannot parse are refused. Narrowing casts were the identity
      (I10, chapter 14's I8); they are now range-checked and may raise
      `badCast`. The Polars translator crashed on duplicate output column
      names (N4); it now keeps them.

    `python/tests/test_backend_semantics.py` pins the native behaviours that
    sverify's translators work around (Polars' floor `%`, NULL on division by
    zero and NULLs-first sort, DuckDB's double `/`, IEEE zeros and
    half-to-even cast, and so on), so an upgrade that changes one of them shows
    up, and pins each fixed gap so that it stays fixed.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 14. [DataFusion's surprising semantics](?file=14_datafusion_semantics.py) · [Contents](?file=00_start_here.py)
    """)
    return


if __name__ == "__main__":
    app.run()

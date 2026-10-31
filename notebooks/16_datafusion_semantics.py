# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "duckdb",
#     "ibis-framework==12.0.0",
#     "marimo",
#     "numpy",
#     "polars",
#     "sverify",
# ]
#
# [tool.uv.sources]
# sverify = { path = "../python", editable = true }
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="full", app_title="16. DataFusion's surprising semantics")


@app.cell(hide_code=True)
def _():
    import marimo as mo

    return (mo,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 15. [What is proved, what is trusted](?file=15_trust.py) · [Contents](?file=00_start_here.py) · 17. [One expression, many engines](?file=17_backend_semantics.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 16. DataFusion's surprising semantics, against the Lean model

    `sverify` proves things about a pipeline's Substrait plan in Lean and then
    runs that plan on **DataFusion**. The proofs are about Lean's semantics
    (`Rel.eval`, `Expr.eval` and the runtime-error model in `Safety.lean`). They
    say something about the real output only if DataFusion computes the same
    thing. This notebook collects every place where DataFusion's behaviour is
    surprising, and checks each one against the model.

    Every **DataFusion**, **DuckDB**, **Polars** and **Lean** cell below is
    computed live when the notebook runs, on the DataFusion version `sverify`
    pins. The "SQL standard" column is prose. The Lean column is one of:

    * *rows*: what `Rel.eval` gives on the same data. The plan is the one
      DataFusion produced, with the tables inlined, run through `substrait-check`.
    * *refused*: the checker rejects the plan, so nothing is proved about it.
    * *verify*: what `sverify.verify` claims, such as "proved", the runtime
      issues it found, or warnings.

    Each quirk is tagged:

    * **agree**: DataFusion does what the model says, however odd that is.
    * **handled**: they differ, but the project copes: it refuses the plan,
      reports an issue, has a precondition, or works around it with a shim.
    * **GAP**: they differ, and nothing stops a proof from being wrong about
      DataFusion's output, or from claiming that no runtime error can happen
      when one does.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Soundness gaps found

    The table below is built from the catalogue further down: it lists every
    entry tagged **GAP**. The most serious ones are where `verify` reports
    `proved` (meaning no runtime error can happen) but DataFusion fails, or
    where a postcondition is proved but DataFusion's output breaks it.
    """)
    return


@app.cell(hide_code=True)
def _(catalogue, mo, render):
    # Most severe first: false proofs on common queries, then false "no runtime
    # error" claims, then rarer mismatches.
    _severity = [
        "F6",
        "E4",
        "E5",
        "I6",
        "I7",
        "I4",
        "S6",
        "N7",
        "I11",
        "T3",
        "I9",
        "F7",
    ]
    _gaps = sorted(
        (q for q in catalogue if q.tag == "GAP"),
        key=lambda q: _severity.index(q.id) if q.id in _severity else len(_severity),
    )
    mo.vstack(
        [
            mo.md(
                f"**{len(_gaps)} gaps** among {len(catalogue)} quirks "
                f"({sum(q.tag == 'agree' for q in catalogue)} agree, "
                f"{sum(q.tag == 'handled' for q in catalogue)} handled)."
            ),
            render(_gaps),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Setup

    One small table per topic. They are registered both in DataFusion (via
    `sverify`) and in DuckDB, and are available as Polars frames. Lean gets
    the same rows, inlined into the plan as a Substrait virtual table.
    `sverify` stores doubles as the model has them (one zero, one NaN), so
    the float table has no negative zero or negative NaN. The queries make
    them with `-v`.
    """)
    return


@app.cell
def _():
    import datetime as dt

    import numpy as np
    import pyarrow as pa

    def ints(**cols):
        return pa.table({k: pa.array(v, pa.int64()) for k, v in cols.items()})

    nan_payloads = np.array([0x7FF8000000000001, 0x7FF8000000000000], dtype=np.uint64)
    tables = {
        "n": ints(x=[1, None, 2]),
        "s": ints(y=[1, None]),
        "e": ints(x=[]),
        "f": pa.table({"v": [1.0, float("nan"), 0.0, float("inf"), float("-inf"), None]}),
        "nanp": pa.table({"v": pa.array(nan_payloads.view(np.float64))}),
        "big53": ints(a=[2**53 + 1], b=[1]),
        "t": ints(a=[5, 0], b=[1, 0]),
        "dm": ints(a=[-7, 7], b=[2, -2]),
        "dz": pa.table({"a": [1.0, -1.0, 0.0], "b": [0.0, 0.0, 0.0]}),
        "r": pa.table({"v": [2.7, -2.7, 2.5, -2.5]}),
        "mixed": pa.table({"a": pa.array([1], pa.int64()), "f": [0.5]}),
        "str5": pa.table({"s": ["5", "05"]}),
        "m": ints(a=[-(2**63), 5]),
        "mx": ints(a=[2**63 - 1, -(2**63)]),
        "pn": ints(a=[None, 2]),
        "i32": pa.table({"a": pa.array([2**31 - 1], pa.int32()), "b": pa.array([1], pa.int32())}),
        "u8": pa.table({"a": pa.array([0], pa.uint8()), "b": pa.array([1], pa.uint8())}),
        "str": pa.table({"s": ["b", "B", "a", "", None, "é", "é", "🎉", "Z"]}),
        "ts": pa.table({"t": pa.array([dt.datetime(2024, 1, 31)], pa.timestamp("us"))}),
        "z": pa.table(
            {
                "t": pa.array(
                    [dt.datetime(2024, 3, 30, 12, 0, tzinfo=dt.UTC)],
                    pa.timestamp("us", tz="Europe/Berlin"),
                )
            }
        ),
        "w": ints(g=[1, 1, 1, 2], o=[1, 2, 2, 1], v=[10, 20, 30, 40]),
        # 30 000 rows in 8 partitions, for sort ties and LIMIT.
        "big": ints(k=[i % 3 for i in range(30000)], i=list(range(30000))),
    }
    return dt, pa, tables


@app.cell(hide_code=True)
def _(dt, pa, tables):
    import copy
    import json
    import subprocess
    from dataclasses import dataclass, field
    from typing import Any

    import duckdb
    import polars as pl
    import sverify as sv
    from sverify.engine import (
        checker_path,
        put_table,
        run_substrait_json,
        substrait_json,
    )
    from sverify.incremental import arrow_rows
    from sverify.testing import inline_tables

    con = sv.connect()
    for _name, _t in tables.items():
        if _name == "big":
            # Several partitions, as a real table would have.
            con.datafusion.register_record_batches(
                _name, [[b] for b in _t.to_batches(max_chunksize=len(_t) // 8)]
            )
        else:
            put_table(con, _name, _t)
    duck = duckdb.connect()
    for _name, _t in tables.items():
        duck.register(_name, _t)
    P = {k: pl.from_arrow(t) for k, t in tables.items()}

    def show(v: object) -> str:
        if v is None:
            return "NULL"
        if isinstance(v, float):
            return repr(v)
        if isinstance(v, dt.datetime):
            return v.isoformat(sep=" ")
        if isinstance(v, str):
            return repr(v)
        return str(v)

    def fmt(rows: list[tuple]) -> str:
        if not rows:
            return "(no rows)"
        if all(len(r) == 1 for r in rows):
            text = ", ".join(show(r[0]) for r in rows)
        else:
            text = ", ".join("(" + ", ".join(map(show, r)) + ")" for r in rows)
        return text if len(text) < 160 else text[:157] + "…"

    def short_error(e: Exception) -> str:
        msg = str(e).replace("DataFusion error: ", "").splitlines()[0]
        return "error: " + (msg if len(msg) < 110 else msg[:107] + "…")

    def run_df(sql: str) -> str:
        """The query's rows on DataFusion, through SQL."""
        try:
            return fmt(arrow_rows(con.datafusion.sql(sql).to_arrow_table()))
        except Exception as e:
            return short_error(e)

    def run_duck(sql: str) -> str:
        try:
            return fmt(duck.sql(sql).fetchall())
        except Exception as e:
            return short_error(e)

    def run_polars(f) -> str:
        try:
            return fmt(f(P).rows())
        except Exception as e:
            return short_error(e)

    def naive_utc(v: object) -> object:
        if isinstance(v, dt.datetime) and v.tzinfo is not None:
            return v.astimezone(dt.timezone.utc).replace(tzinfo=None)
        return v

    def checker(plan: dict) -> subprocess.CompletedProcess:
        return subprocess.run(
            [str(checker_path()), "/dev/stdin"],
            input=json.dumps(plan),
            capture_output=True,
            text=True,
            check=False,
        )

    def lean_rows(sql: str) -> str:
        """`Rel.eval` of DataFusion's plan for `sql`, on the same rows. Lean
        prints doubles with a `d`, and ±0.0 as their raw codes ±1."""
        try:
            plan = json.loads(substrait_json(con, sql))
        except Exception as e:
            return "no plan: " + short_error(e)
        refused = checker(plan)
        if refused.returncode != 0:
            return "refused: " + refused.stderr.strip().removeprefix("error: ")[:110]
        rows = {
            name: [tuple(naive_utc(v) for v in r) for r in arrow_rows(t)]
            for name, t in tables.items()
        }
        out = checker(inline_tables(copy.deepcopy(plan), rows)).stdout
        got = [
            line.strip()
            for line in out.split("rows (")[1].splitlines()[1:]
            if line.startswith("  (")
        ]
        text = ", ".join(r[1:-1] if r.count(",") == 0 else r for r in got) or "(no rows)"
        return text if len(text) < 160 else text[:157] + "…"

    def prove(sql: str, requires=(), ensures=(), on: str = "t") -> str:
        """What `sverify.verify` claims about `sql`, with `requires` on table `on`."""
        schema = {f.name: f.type for f in tables[on].schema}
        dtypes = {
            n: "uint8"
            if t == pa.uint8()
            else "int32"
            if t == pa.int32()
            else "timestamp('Europe/Berlin', 6)"
            if isinstance(t, pa.TimestampType) and t.tz
            else "float64"
            if t == pa.float64()
            else "int64"
            for n, t in schema.items()
        }
        try:
            r = sv.verify(
                sql,
                requires={on: list(requires)},
                ensures=list(ensures),
                tables={on: dtypes},
            )
        except Exception as e:
            return "refused: " + str(e)[:110]
        parts = [f"{c.label}: {'proved' if c.proved else 'not proved'}" for c in r.ensures]
        parts += [f"may fail: {i.kind}" for i in r.errors]
        parts += [f"warning: {i.kind}" for i in r.warnings]
        if not r.deterministic:
            parts.append("not deterministic (ties)")
        verdict = "proved ✓" if r.proved else "not proved"
        return f"verify: {verdict}" + (
            " — " + "; ".join(parts) if parts else " (no runtime issue possible)"
        )

    @dataclass
    class Q:
        id: str
        title: str
        sql: str
        tag: str
        why: str
        std: str = ""
        duck: str | None = None
        polars: Any = None
        lean: Any = "rows"
        df: Any = None
        out: dict = field(default_factory=dict)

        def run(self) -> "Q":
            self.out["df"] = self.df() if callable(self.df) else run_df(self.sql)
            others = [f"SQL: {self.std}"] if self.std else []
            if self.duck is not None:
                others.append("DuckDB: " + run_duck(self.sql if self.duck == "same" else self.duck))
            if self.polars is not None:
                others.append("Polars: " + run_polars(self.polars))
            self.out["others"] = others
            self.out["lean"] = (
                lean_rows(self.sql)
                if self.lean == "rows"
                else self.lean()
                if callable(self.lean)
                else self.lean
            )
            return self

    return P, Q, con, lean_rows, pl, prove, run_substrait_json, substrait_json, sv


@app.cell(hide_code=True)
def _(mo):
    import html

    COLORS = {"agree": "#2e8b57", "handled": "#2f6db5", "GAP": "#c0392b"}

    def render(qs):
        """A compact table: one row per quirk."""
        cell = "text-align:left;vertical-align:top;padding:4px 12px 4px 0"
        mono = "font-family:var(--monospace-font, monospace);font-size:0.8rem"
        head = "".join(
            f"<th style='{cell}'>{c}</th>"
            for c in [
                "",
                "quirk",
                "query",
                "DataFusion (live)",
                "SQL / DuckDB / Polars",
                "Lean",
                "verdict",
            ]
        )
        body = []
        for q in qs:
            color = COLORS[q.tag]
            others = "<br>".join(html.escape(o) for o in q.out["others"]) or "—"
            body.append(
                "<tr style='border-top:1px solid #8883'>"
                f"<td style='{cell};opacity:.6'>{q.id}</td>"
                f"<td style='{cell};min-width:9rem'>{html.escape(q.title)}</td>"
                f"<td style='{cell};{mono};max-width:22rem'>{html.escape(q.sql)}</td>"
                f"<td style='{cell};{mono};max-width:16rem'>{html.escape(q.out['df'])}</td>"
                f"<td style='{cell};font-size:0.8rem;max-width:16rem'>{others}</td>"
                f"<td style='{cell};{mono};max-width:16rem'>{html.escape(q.out['lean'])}</td>"
                f"<td style='{cell};font-size:0.85rem;max-width:20rem'>"
                f"<b style='color:{color}'>{q.tag}</b> {html.escape(q.why)}</td>"
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
    ## 1. NULL

    SQL's `NULL` means "unknown", and it uses three-valued logic: a comparison
    with `NULL` is neither true nor false, but `NULL`. A `WHERE` keeps a row
    only if the condition is *true*, so a `NULL` condition drops the row just
    like `false` does. Lean models this exactly (`and3`, `or3`,
    `Value.isTrue`).

    * **N1–N2**: `x IN (1, NULL)` means `x = 1 OR x = NULL`. So `NOT IN` a
      list that contains a `NULL` is never true. This is standard SQL, and a
      classic trap.
    * **N3**: the same with a subquery. DataFusion 51 gets this **wrong**:
      it returns rows for `x NOT IN (SELECT y …)` even when `y` contains a
      `NULL`. It runs the query as an ordinary anti join, without SQL's
      "null-aware" rule. DuckDB gives the standard answer, which is no rows.
      Lean's parser does not accept `NOT IN (subquery)`, so no proof
      depends on it. Positive `IN (subquery)` becomes a semi join, which is
      correct.
    * **N4**: aggregates over no rows: `COUNT` is 0, but `SUM`, `AVG` and
      `MIN` are `NULL`, not 0. The model has no aggregates yet, so it
      refuses these plans.
    * **N5–N6**: `NULL` join keys never match with `=`, but `IS NOT DISTINCT
      FROM` treats two `NULL`s as equal. `DISTINCT` and `GROUP BY` put all
      `NULL`s into one group, so for grouping `NULL` *does* equal `NULL`.
    * **N7**: `GREATEST`/`LEAST` skip `NULL`s, as in PostgreSQL, while
      Snowflake returns `NULL`, and Lean agrees. But `x || 'a'` with an
      integer `x` is a **gap**. The cast of `x` to a string is missing from
      the plan (see F6), so Lean computes `NULL` on every row.
    """)
    return


@app.cell(hide_code=True)
def _(P, Q, pl, prove, render):
    nulls = [
        Q(
            "N1",
            "comparisons with NULL",
            "SELECT x = y AS eq, x <> 1 AS ne, x IS NOT DISTINCT FROM y AS nd FROM n CROSS JOIN s "
            "WHERE x IS NULL AND y IS NULL",
            "agree",
            "`=` propagates NULL; `IS NOT DISTINCT FROM` is never NULL (`notDistinct` in Parse.lean).",
            std="NULL, NULL, true",
            duck="same",
            polars=lambda P: pl.select(
                eq=pl.lit(None, pl.Int64) == pl.lit(None, pl.Int64),
                nd=pl.lit(None, pl.Int64).eq_missing(pl.lit(None, pl.Int64)),
            ),
        ),
        Q(
            "N2",
            "NOT IN a list with NULL",
            "SELECT x FROM n WHERE x NOT IN (1, NULL)",
            "agree",
            "IN is parsed as an OR of `=`, so the NULL makes NOT IN never true.",
            std="no rows",
            duck="same",
        ),
        Q(
            "N3",
            "NOT IN a subquery with NULL",
            "SELECT x FROM n WHERE x NOT IN (SELECT y FROM s)",
            "handled",
            "DataFusion bug (no null-aware anti join). The checker refuses `NOT IN (subquery)`, "
            "so nothing is proved. Use NOT EXISTS, which DataFusion gets right.",
            std="no rows (s contains NULL)",
            duck="same",
        ),
        Q(
            "N4",
            "aggregates over no rows",
            "SELECT count(*) AS a, count(x) AS b, sum(x) AS c, avg(x) AS d FROM e",
            "handled",
            "Aggregates are not in the model yet (`measures` are refused). Worth keeping in mind for Phase 4: SUM of nothing is NULL.",
            std="0, 0, NULL, NULL",
            duck="same",
            polars=lambda P: P["e"].select(
                a=pl.len(),
                b=pl.col("x").count(),
                c=pl.col("x").sum(),
                d=pl.col("x").mean(),
            ),
        ),
        Q(
            "N5",
            "NULL join keys",
            "SELECT n.x, s.y FROM n JOIN s ON n.x IS NOT DISTINCT FROM s.y",
            "agree",
            "With `=` NULL keys never match; with IS NOT DISTINCT FROM they do, and Lean agrees.",
            std="(1, 1), (NULL, NULL)",
            duck="same",
        ),
        Q(
            "N6",
            "DISTINCT on NULL",
            "SELECT DISTINCT x FROM (SELECT x FROM n UNION ALL SELECT x FROM n)",
            "agree",
            "`dedup` compares Values with `=` on the Lean side, where NULL equals NULL.",
            std="1, 2, NULL (one NULL group)",
            duck="same",
            polars=lambda P: pl.concat([P["n"], P["n"]]).unique(maintain_order=True),
        ),
        Q(
            "N7",
            "GREATEST skips NULL; int || text",
            "SELECT x, greatest(x, 0) AS g, x || 'a' AS p FROM n",
            "GAP",
            "GREATEST agrees (`pick` skips NULLs). But `x || 'a'` reaches Lean without the cast of x to a string "
            "(root cause of F6), so Lean computes NULL and `verify` proves `p IS NULL`.",
            std="vendor-specific; Snowflake gives NULL for GREATEST",
            duck="same",
        ),
    ]
    render([q.run() for q in nulls])
    return (nulls,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 2. Floating point

    IEEE 754, the standard for floating-point numbers, has two odd values:
    `NaN` ("not a number", for example `0/0`) and a negative zero, `-0.0`.
    IEEE says that `NaN` equals nothing, not even itself, and that
    `-0.0 = 0.0`. DataFusion does **not** follow IEEE for comparisons. It uses
    Arrow's *total order* (`f64::total_cmp`):

    `-NaN < -∞ < … < -0.0 < 0.0 < … < ∞ < NaN`, and `NaN = NaN`.

    The model does not follow DataFusion here. SQL engines (PostgreSQL,
    DuckDB, Spark, Snowflake) have **one NaN**, equal to itself and above
    `∞`, and **one zero**, and so does Lean's `Float.lean` (chapter 12): the
    least surprising choice. So:

    * **F1–F2**: `NaN = NaN` and `NaN > ∞` are true everywhere. DataFusion
      says `-0.0 = 0.0` is **false** and sorts a negative NaN *first*; the
      model says `-0.0` is `0.0`, and a negative NaN is NaN.
    * **F3**: `WHERE v > 1e308` keeps `NaN` rows; DataFusion's `DISTINCT`
      keeps `-0.0` and `0.0` apart, the model's keeps one zero.

    `sverify` stores DataFusion's tables canonical (no `-0.0`, positive NaN),
    and the plans Lean writes wrap each double operation in
    `nanvl(x + 0.0, 'NaN')`, so its engines, DataFusion's included, compute
    what the model says. What remains a **GAP** is DataFusion running a query
    itself (Ibis's `execute`, or a transform's output): a zero or NaN it
    *computes* is compared by the total order inside that query, so
    `filter(-x < 0)` keeps `x = 0` there and the model drops it.
    * **F4**: dividing a double by zero is not an error: you get ±∞ or NaN.
      (Integer division by zero *is* an error, see §3.)
    * **F5**: `CAST(2.7 AS BIGINT)` truncates to 2. DuckDB rounds it to 3.
      `ROUND` rounds halves away from zero, while Polars and Python round
      them to even.
    * **F6**: comparing an integer column with a double. `sverify` builds
      the Substrait plan from DataFusion's `logical_plan()`. That plan is
      taken *before* DataFusion's analyzer inserts the implicit type casts
      (type coercion), so it compares `a > f` with **no cast**. DataFusion's
      consumer redoes the coercion when it reads the plan back, so DataFusion
      itself never notices. Lean's parser only converts integer *constants*
      next to a double. So it compares the raw integer
      `1` with the *code* of `0.5`, which is a huge integer, and **proves**
      that `1 > 0.5` is false. The Ibis expression `t.a > t.f` produces
      exactly this plan. This is the most serious gap in the catalogue,
      because mixing integer and double columns is common. The same missing
      casts break `int || string` (N7) and `string = int` (I11).
    * **F9**: with explicit casts on both sides, the integer is converted
      with rounding, so `2^53 + 1` and `2^53` become the same double. Lean
      agrees.
    * **F7**: the total order also tells apart NaNs with different *payloads*
      (the unused bits of a NaN). The model has a single NaN, and `sverify`
      stores every NaN as that one, so DataFusion sees them equal.
    * **F8**: `MIN`/`MAX` follow the total order too, so `MAX` of a column
      with a NaN is NaN. The model has no aggregates yet.
    """)
    return


@app.cell(hide_code=True)
def _(P, Q, pl, prove, render):
    floats = [
        Q(
            "F1",
            "NaN and -0.0 comparisons",
            "SELECT v, v = v AS self, -v = v AS neg_eq, -v < v AS neg_lt FROM f WHERE v = 0 OR isnan(v)",
            "GAP",
            "DataFusion's total order: -0.0 < 0.0. The model has one zero (code 0): -v = v for v = 0. "
            "sverify's engines canonicalize; DataFusion running the query itself does not.",
            std="IEEE: NaN ≠ NaN, -0.0 = 0.0",
            duck="SELECT v, v = v, -v = v, -v < v FROM f WHERE v = 0 OR isnan(v)",
            polars=lambda P: (
                P["f"]
                .filter((pl.col("v") == 0) | pl.col("v").is_nan())
                .select(
                    "v",
                    same=pl.col("v") == pl.col("v"),
                    neg_eq=-pl.col("v") == pl.col("v"),
                )
            ),
        ),
        Q(
            "F2",
            "ORDER BY with NaN, -NaN, ±0, ±∞",
            "SELECT w FROM (SELECT v AS w FROM f UNION ALL SELECT -v FROM f) ORDER BY w",
            "GAP",
            "DataFusion sorts -NaN first and -0.0 before 0.0; the model has one NaN (last) and one zero.",
            duck="same",
            polars=lambda P: pl.concat([P["f"], P["f"].select(-pl.col("v"))]).sort("v"),
        ),
        Q(
            "F3",
            "NaN passes `> big`; DataFusion's ±0 keys differ",
            "SELECT DISTINCT w FROM (SELECT v AS w FROM f UNION ALL SELECT -v FROM f) WHERE w > 1e308 OR w = 0",
            "GAP",
            "Lean keeps NaN and one zero; DataFusion's DISTINCT keeps -0.0 and 0.0 apart.",
            std="IEEE: NaN fails every comparison; -0.0 and 0.0 are one value",
            duck="same",
        ),
        Q(
            "F4",
            "double division by zero",
            "SELECT a / b AS q FROM dz",
            "agree",
            "fdiv is computed with native floats: ±∞ and NaN, no error.",
            std="IEEE: ±∞, NaN (some engines raise)",
            duck="same",
            polars=lambda P: P["dz"].select(q=pl.col("a") / pl.col("b")),
        ),
        Q(
            "F5",
            "casts truncate, ROUND half away",
            "SELECT v, CAST(v AS BIGINT) AS i, round(v) AS r FROM r",
            "agree",
            "`ftoi` truncates toward zero; `fround` rounds halves away (Rounding.lean). NaN/∞ casts are a reported error.",
            duck="same",
            polars=lambda P: P["r"].select(
                "v", i=pl.col("v").cast(pl.Int64), r=pl.col("v").round()
            ),
        ),
        Q(
            "F6",
            "int column vs double: no cast",
            "SELECT a, f, a > f AS gt FROM mixed",
            "GAP",
            "`sverify.engine.substrait_json` produces Substrait from DataFusion's *unanalysed* logical plan, "
            "before type coercion adds `CAST(a AS DOUBLE)`. Lean compares the integer 1 with the *code* of 0.5 "
            "and proves `NOT gt`. Ibis's `t.a > t.f` hits it too.",
            std="1 > 0.5 is true",
            duck="same",
            polars=lambda P: P["mixed"].select("a", "f", gt=pl.col("a") > pl.col("f")),
            lean=lambda: prove(
                "SELECT a > f AS gt FROM mixed",
                requires=["a = 1", "f = 0.5"],
                ensures=["NOT gt"],
                on="mixed",
            ),
        ),
        Q(
            "F9",
            "int to double rounds",
            "SELECT CAST(a AS DOUBLE) = CAST(a - 1 AS DOUBLE) AS eq FROM big53",
            "agree",
            "With explicit casts on both sides Lean's `itof` rounds 2^53 + 1 like DataFusion. (Without the cast on `a`, see F6.)",
            std="implementation-defined",
            duck="same",
        ),
        Q(
            "F7",
            "NaN payloads are distinct",
            "SELECT a.v = b.v AS eq FROM nanp a CROSS JOIN nanp b",
            "handled",
            "DataFusion tells NaN payloads apart (and DISTINCT keeps both), but `sverify` stores "
            "every NaN as the one NaN (`engine.canonical`), as the model has it, so all are equal.",
            std="IEEE: NaN ≠ NaN always",
            duck="same",
            lean="all true (both values decode to the one positive NaN code)",
        ),
        Q(
            "F8",
            "MAX with NaN",
            "SELECT max(v) AS mx, min(-v) AS mn FROM f",
            "handled",
            "Aggregates are refused for now; when they arrive, MAX/MIN must follow the total order.",
            duck="same",
            polars=lambda P: P["f"].select(mx=pl.col("v").max(), mn=(-pl.col("v")).min()),
        ),
    ]
    render([q.run() for q in floats])
    return (floats,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 3. Integers

    The model's integers are unbounded (`Int`), and `Safety.lean` reports
    where DataFusion's 64-bit integers would behave differently. DataFusion
    has four kinds of failure, and they are inconsistent:

    * **errors**: integer division or remainder by zero, `MIN / -1`, `abs(MIN)`,
      a negative or oversized `power`, and an out-of-range cast;
    * **silent wrap-around**: `+`, `-`, `*` and negation. `MAX + 1` gives
      `MIN`. Lean reports these as warnings. Note that `Report.proved` ignores
      warnings, so look at `report.warnings` as well.

    Division truncates toward zero, so `-7 / 2 = -3` and `-7 % 2 = -1`.
    DuckDB's `/` on integers returns a double instead, and Python and Polars
    floor (`-7 // 2 = -4`).

    The gaps are all about **types narrower than 64 bits**. The parser maps
    `i8`, `i16`, `i32` and `i64` to one integer kind. But DataFusion does
    `INT + INT` in 32 bits, and Substrait has no unsigned types: DataFusion
    writes `UINT8` as `i8` plus a "type variation" that Lean ignores. So:

    * **I6**: `int32 + int32` wraps at 2^31, and `verify` proves `a + b >= 0`
      with no warning, because the sum does fit in 64 bits.
    * **I7**: `uint8 0 - 1` is 255 in DataFusion. Lean computes -1 and proves
      `d < 0`.
    * **I8**: `CAST(bigint AS INT)` is parsed as the identity, with no range
      check, but DataFusion raises a cast error.
    * **I4**: `abs(MIN)` is parsed as `IF a < 0 THEN -a ELSE a`, so Lean
      reports only a wrap-around warning, but DataFusion raises an error.
    * **I9**: DataFusion has `power(NULL, 0) = 1` for a column, while Lean's
      `ipow` propagates `NULL`. The contract checker's abstraction is too
      coarse to prove anything false from this, but `Rel.eval` (and so the
      DuckDB and Polars backends) disagrees with DataFusion.
    """)
    return


@app.cell(hide_code=True)
def _(P, Q, pl, prove, render):
    integers = [
        Q(
            "I1",
            "64-bit + wraps silently",
            "SELECT a + 1 AS s, -a AS neg FROM mx",
            "handled",
            "Reported as a `may wrap around` warning (Safety.lean, `Issue.wraps`). Warnings do not make `proved` false.",
            std="error (numeric value out of range)",
            duck="same",
            polars=lambda P: P["mx"].select(s=pl.col("a") + 1),
            lean=lambda: prove("SELECT a + 1 AS s FROM mx", on="mx"),
        ),
        Q(
            "I2",
            "integer division by zero",
            "SELECT a / b AS q, a % b AS r FROM t",
            "handled",
            "A hard error in DataFusion (unlike doubles). Reported as `division by zero`; `a / NULLIF(b, 0)` is proved safe.",
            std="error",
            duck="same",
            lean=lambda: prove("SELECT a / b AS q FROM t", requires=["a >= 0"]),
        ),
        Q(
            "I3",
            "truncating division and modulo",
            "SELECT a, b, a / b AS q, a % b AS r FROM dm",
            "agree",
            "`Int.tdiv` / `Int.tmod`. Ibis's `//` floors; engine.py compiles it to an exact integer CASE.",
            std="truncate (SQL:2003)",
            duck="SELECT a, b, a / b, a // b, a % b FROM dm",
            polars=lambda P: P["dm"].select(
                "a", "b", q=pl.col("a") // pl.col("b"), r=pl.col("a") % pl.col("b")
            ),
        ),
        Q(
            "I4",
            "abs(MIN) fails",
            "SELECT abs(a) AS x FROM m",
            "GAP",
            "DataFusion raises an overflow error; Lean parses abs as `IF a < 0 THEN -a`, a wrap warning only, so `proved` is true.",
            std="error",
            duck="same",
            lean=lambda: prove("SELECT abs(a) AS x FROM m", on="m"),
        ),
        Q(
            "I5",
            "MIN / -1 and MIN % -1",
            "SELECT a / -1 AS q FROM m",
            "handled",
            "`MIN / -1` is an error (`overflow` issue); `MIN % -1` is 0 in both DataFusion and Lean.",
            duck="same",
            lean=lambda: prove("SELECT a / -1 AS q FROM m", on="m"),
        ),
        Q(
            "I6",
            "INT + INT wraps at 32 bits",
            "SELECT a + b AS s, a + b >= 0 AS ok FROM i32",
            "GAP",
            "The parser forgets integer widths; the wrap check is 64-bit. `s >= 0` is proved without a warning, DataFusion gives a negative sum.",
            std="error",
            duck="same",
            polars=lambda P: P["i32"].select(s=pl.col("a") + pl.col("b")),
            lean=lambda: prove(
                "SELECT a + b AS s FROM i32",
                requires=["a BETWEEN 0 AND 2147483647", "b BETWEEN 0 AND 2147483647"],
                ensures=["s >= 0"],
                on="i32",
            ),
        ),
        Q(
            "I7",
            "UINT8 read as signed",
            "SELECT a - b AS d, a - b < 0 AS neg FROM u8",
            "GAP",
            "Substrait has no unsigned types (DataFusion uses a type variation the parser ignores). Lean computes 0 − 1 = −1 and proves `d < 0`.",
            duck="same",
            lean=lambda: prove(
                "SELECT a - b AS d FROM u8",
                requires=["a = 0", "b = 1"],
                ensures=["d < 0"],
                on="u8",
            ),
        ),
        Q(
            "I8",
            "narrowing CAST fails",
            "SELECT CAST(a AS INT) AS x FROM m",
            "handled",
            "`CAST(bigint AS INT)` raises a CastError in DataFusion. Lean models it as `UnFn.narrow` (it used to read it as the identity): NULL plus a `badCast` issue where the value does not fit, so `verify` reports the possible error.",
            std="error",
            duck="same",
            lean=lambda: prove("SELECT CAST(a AS INT) AS x FROM m", on="m"),
        ),
        Q(
            "I9",
            "power(NULL, 0) = 1",
            "SELECT a, power(a, 0) AS p FROM pn",
            "GAP",
            "DataFusion gives 1 for a NULL base (a literal NULL folds to NULL). Rel.eval gives NULL. Not exploitable by `verify` today, but the semantics disagree.",
            std="NULL",
            duck="same",
        ),
        Q(
            "I10",
            "implicit coercions",
            "SELECT arrow_typeof(a + 1) AS t1, arrow_typeof(row_number() OVER () - 1) AS t2 FROM i32",
            "handled",
            "Literals widen INT to BIGINT; ROW_NUMBER is UInt64 and `ROW_NUMBER() - 1` a Decimal(21,0). Lean has one integer type; tests convert decimals.",
            duck="SELECT typeof(a + 1), typeof(row_number() OVER () - 1) FROM i32",
            lean="n/a (types only)",
        ),
        Q(
            "I11",
            "string = number compares strings",
            "SELECT s, s = 5 AS eq FROM str5",
            "GAP",
            "DataFusion casts the *number* to a string, so '05' = 5 is false (DuckDB casts the string: true). "
            "The plan has no cast (root cause of F6): Lean compares a string with an integer and gets NULL.",
            std="implementation-defined",
            duck="same",
        ),
    ]
    render([q.run() for q in integers])
    return (integers,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 4. Strings

    Strings are compared byte by byte in their UTF-8 encoding, which is the
    same as comparing them by Unicode code point. There is no locale-aware
    *collation*, so `'Z' < 'a'` and `'é'` sorts after `'z'`. Lean compares
    `String`s by code point, which agrees.

    * **S1**: ordering puts upper case before lower case, and `NULL` last.
    * **S2**: `''` (the empty string) and `NULL` are different values (Oracle
      famously treats them as the same).
    * **S3**: `character_length` counts *code points*. An `é` written as one
      code point has length 1. Written as `e` followed by a combining accent,
      it has length 2, though it looks the same. DuckDB's `length` counts
      *grapheme clusters* (what a reader sees as characters) and gives 1.
      Lean counts code points.
    * **S4**: `LIKE` is case-sensitive, and `ILIKE` is not. `LIKE … ESCAPE`
      with anything but a backslash is refused.
    * **S6**: but Lean has **no `<` on strings**. `BinFn.lt` is only defined
      on integers (and float codes), so `s > 'd'` is `NULL` in Lean, and a
      filter on it keeps nothing. `ORDER BY` on strings is fine, because
      sorting uses `Value.le`.
    * **S5**: `upper('ß')` becomes `'SS'`, longer than its input. Lean
      treats `UPPER`/`LOWER` as black boxes, so it assumes nothing about them.
    """)
    return


@app.cell(hide_code=True)
def _(P, Q, pl, prove, render):
    strings = [
        Q(
            "S1",
            "byte-order collation",
            "SELECT s FROM str ORDER BY s",
            "agree",
            "Code-point order = UTF-8 byte order (`Value.le` on strings).",
            std="collation-dependent",
            duck="same",
            polars=lambda P: P["str"].sort("s"),
        ),
        Q(
            "S2",
            "'' is not NULL",
            "SELECT s, s = '' AS empty, s IS NULL AS null FROM str WHERE s = '' OR s IS NULL",
            "agree",
            'Two different Values (`.str ""` and `.null`).',
            std="distinct (Oracle: '' IS NULL)",
            duck="same",
        ),
        Q(
            "S3",
            "length counts code points",
            "SELECT s, character_length(s) AS n FROM str WHERE s IN ('é', 'e\u0301', '🎉')",
            "agree",
            "`String.length` counts code points, like DataFusion and Polars' `len_chars`; DuckDB's `length` counts graphemes.",
            duck="SELECT s, length(s), strlen(s) FROM str WHERE s IN ('é', 'e\u0301', '🎉')",
            polars=lambda P: (
                P["str"]
                .filter(pl.col("s").is_in(["é", "e\u0301", "🎉"]))
                .select("s", n=pl.col("s").str.len_chars())
            ),
        ),
        Q(
            "S4",
            "LIKE is case-sensitive",
            "SELECT s FROM str WHERE s LIKE 'b%'",
            "agree",
            "`Text.like` compares exactly. ILIKE and `LIKE … ESCAPE '#'` are refused.",
            duck="same",
        ),
        Q(
            "S5",
            "upper('ß') grows",
            "SELECT upper('straße') AS u, character_length(upper('straße')) AS n",
            "agree",
            "UPPER/LOWER are black boxes in Text.lean: nothing about their length is assumed.",
            duck="same",
            lean="black box (constant-folded by DataFusion here)",
        ),
        Q(
            "S6",
            "string < and > ",
            "SELECT s, s > 'd' AS gt FROM str WHERE s IS NOT NULL",
            "GAP",
            "Lean's `BinFn.lt` is only defined on integers, so any string `<`, `>`, `<=`, `>=` is NULL. "
            "`verify` proves `gt IS NULL` for `s = 'z'`; a filter `s > 'd'` keeps nothing in Lean.",
            std="true for 'é', 'é', '🎉'",
            duck="same",
            lean=lambda: prove(
                "SELECT s, s > 'd' AS gt FROM str",
                requires=["s = 'z'"],
                ensures=["gt IS NULL"],
                on="str",
            ),
        ),
    ]
    render([q.run() for q in strings])
    return (strings,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 5. Timestamps, time zones and intervals

    Lean models timestamps as microseconds since 1970 and day-to-second
    intervals as microseconds. That is exact for timestamps **without** a
    time zone. An `INTERVAL` in DataFusion has three separate fields (months,
    days, nanoseconds), because a month or a day has no fixed length:

    * **T1**: `Jan 31 + 1 month` is `Feb 29`. DataFusion clamps to the end
      of the month. Lean's `Time.addMonths` does the same (constant months,
      added to a date or timestamp before any days).
    * **T2**: `INTERVAL '1 day' = INTERVAL '24 hours'` is **false**, since the
      fields are compared separately.
    * **T3**: on a timestamp *with* a time zone, `+ INTERVAL '1 day'` keeps
      the local wall-clock time. Across a daylight-saving switch that is only
      23 hours. Lean always adds 86 400 s, so in Berlin on 30 March 2024 it
      says `t + 1 day >= t + 24 hours` is true, while DataFusion says false.
      Substrait's `precisionTimestampTz` type does not even record the zone
      (DataFusion reads it from the table).
    * **T4**: `date_part`/`date_trunc` on a zoned timestamp are refused.
    * **T5**: the SQL literal `TIMESTAMP '…'` has nanosecond precision.
      Lean accepts only microseconds, and Ibis casts to them.
    """)
    return


@app.cell(hide_code=True)
def _(Q, prove, render):
    times = [
        Q(
            "T1",
            "month arithmetic clamps",
            "SELECT t + INTERVAL '1 month' AS m FROM ts",
            "handled",
            "Month/year intervals are refused by the parser.",
            std="Feb 29 (or an error, depending on engine)",
            duck="same",
        ),
        Q(
            "T2",
            "1 day ≠ 24 hours",
            "SELECT INTERVAL '1 day' = INTERVAL '24 hours' AS eq",
            "agree",
            "Folded to a constant by DataFusion before Lean sees it; Lean normalizes intervals, which only matters with time zones (T3).",
            duck="same",
            lean="n/a (constant-folded)",
        ),
        Q(
            "T3",
            "+1 day across DST",
            "SELECT t, t + INTERVAL '1 day' >= t + INTERVAL '24 hours' AS ok FROM z",
            "GAP",
            "DataFusion is DST-aware on zoned timestamps (the day is 23 h); Lean adds 86 400 s. Filters on such expressions keep different rows.",
            std="local wall-clock (23 h)",
            duck="SET TimeZone = 'Europe/Berlin'; SELECT TIMESTAMPTZ '2024-03-30 12:00:00+00' + INTERVAL '1 day' "
            ">= TIMESTAMPTZ '2024-03-30 12:00:00+00' + INTERVAL '24 hours'",
        ),
        Q(
            "T4",
            "date_part on a zoned timestamp",
            "SELECT date_part('hour', t) AS h FROM z",
            "handled",
            "Refused: `date_part` and `date_trunc` are only modelled on timestamps without a zone.",
            duck="SELECT hour(t) FROM z",
        ),
        Q(
            "T5",
            "TIMESTAMP literals are ns",
            "SELECT arrow_typeof(TIMESTAMP '2024-03-31 02:30:00') AS ty",
            "agree",
            "DataFusion writes the literal as a cast of a string to a ns timestamp; Lean reads the string in µs, which is exact.",
            lean=lambda: prove(
                "SELECT t FROM ts WHERE t > TIMESTAMP '2024-01-01 00:00:00'", on="ts"
            ),
        ),
    ]
    render([q.run() for q in times])
    return (times,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 6. Order, LIMIT and windows

    A table is a *bag*: its rows have no order. An engine runs on several
    partitions in parallel and merges the results, so any order you did not
    ask for is an accident.

    * **O1**: by default `ASC` puts `NULL`s last and `DESC` puts them first,
      as in PostgreSQL. DuckDB puts them last both ways, and Polars puts them
      first. The plan always states the direction, so Lean reads it from
      there.
    * **O2**: `ORDER BY` is **not stable**: rows that tie on the sort key come
      out in no particular order, which is not the input order. Lean's
      `Rel.eval` uses a stable sort, which is *one* valid outcome. Plans with
      `FETCH` are not maintained incrementally, and a window whose result
      depends on ties makes `verify` report "not deterministic".
    * **O3**: `LIMIT` without `ORDER BY` returns *some* rows, and which ones
      may change between runs. This is handled in the same way.
    * **O4**: window *frame* defaults. With an `ORDER BY`, the default frame
      is `RANGE BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW`, and `RANGE`
      includes the current row's *peers*. So a "running sum" jumps by both
      tied rows at once, and `last_value` returns the last tied row, not the
      current one. Without an `ORDER BY`, the frame is the whole partition.
      The model reads the frame of each window function from the plan
      (`Window.Frame`: `RANGE` frames are a condition on the sort key, peers
      included). DataFusion's Substrait producer writes `RANGE` offsets as
      `UNBOUNDED`, so SQL with them is refused; its sliding `AVG` of an
      emptied frame is NaN and its sliding `MIN` of NULLs is stale, so those
      are refused too; and its `NTILE` is `⌊i·min(k, n)/n⌋ + 1`, which the
      model follows.
    * **O5**: `LAG` over ties, or without `ORDER BY`, depends on the engine's
      order. `verify` says so, unless the partition and sort columns form a
      declared key.
    """)
    return


@app.cell(hide_code=True)
def _(P, Q, con, pl, prove, render):
    def _tie_order():
        runs = [
            [
                r["i"]
                for r in con.datafusion.sql("SELECT i FROM big ORDER BY k")
                .to_arrow_table()
                .slice(0, 6)
                .to_pylist()
            ]
            for _ in range(2)
        ]
        return f"first rows of k = 0: {runs[0]}; input order would be 0, 3, 6, …"

    order = [
        Q(
            "O1",
            "default NULL placement",
            "SELECT x FROM n ORDER BY x DESC",
            "agree",
            "Directions are explicit in the plan (`SORT_DIRECTION_DESC_NULLS_FIRST`); Lean reads them.",
            std="implementation-defined",
            duck="same",
            polars=lambda P: P["n"].sort("x", descending=True),
        ),
        Q(
            "O2",
            "sort is not stable",
            "SELECT i FROM big ORDER BY k",
            "handled",
            "Rel.eval picks the stable order; FETCH plans are not incremental and window ties are flagged.",
            df=_tie_order,
            std="unspecified order of ties",
            lean="stable: 0, 3, 6, … (one of the allowed outcomes)",
        ),
        Q(
            "O3",
            "LIMIT without ORDER BY",
            "SELECT k, i FROM big LIMIT 3",
            "handled",
            "Lean takes the first rows in list order; nothing incremental or key-related depends on which rows.",
            std="any 3 rows",
            lean="the first 3 rows of the table",
        ),
        Q(
            "O4",
            "window frame defaults",
            "SELECT g, o, v, sum(v) OVER (PARTITION BY g ORDER BY o) AS run, last_value(v) OVER (PARTITION BY g ORDER BY o) AS lv FROM w ORDER BY g, o, v",
            "handled",
            "RANGE frames include peers. Aggregate window functions are refused.",
            std="same (RANGE … CURRENT ROW)",
            duck="same",
        ),
        Q(
            "O5",
            "LAG over ties",
            "SELECT g, o, v, lag(v) OVER (PARTITION BY g ORDER BY o) AS l FROM w ORDER BY g, o, v",
            "handled",
            "`verify` reports that the result is not deterministic unless `unique(g, o)` is required.",
            duck="same",
            lean=lambda: prove(
                "SELECT g, o, v, lag(v) OVER (PARTITION BY g ORDER BY o) AS l FROM w",
                ensures=["l IS NULL OR l >= 0"],
                on="w",
            ),
        ),
    ]
    render([q.run() for q in order])
    return (order,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 7. When does DataFusion evaluate an expression?

    This decides whether a runtime error can happen. `Safety.lean` states
    the trusted assumptions: `AND`/`OR` evaluate both sides, filters may be
    merged and pushed down (so a guard in an inner `WHERE` does not protect
    an outer one), and **`CASE` only evaluates the branch a row takes**. The
    first two hold, and the checker reports them (**E1–E2**). The third has
    exceptions:

    * **E3**: a `CASE` that returns a number really is lazy:
      `CASE WHEN b <> 0 THEN a / b END` never divides by zero.
    * **E4**: a `CASE` that returns a **boolean** is rewritten by
      DataFusion's simplifier into `AND`/`OR`, which evaluate both sides. So
      `CASE WHEN b <> 0 THEN a / b > 1 ELSE false END` becomes
      `b <> 0 AND a / b > 1`, and divides by zero. The Substrait plan Lean sees
      still has the `CASE`, and `verify` says it cannot fail. This happens in
      a projection too, and also with `ELSE NULL`, with `ELSE true`, and with
      a missing `ELSE`.
    * **E5**: `COALESCE(b, a / b)` evaluates `a / b` even where `b` is not
      `NULL`. Lean models `COALESCE` as a `CASE`, so it says the division only
      happens where `b` is `NULL`.
    """)
    return


@app.cell(hide_code=True)
def _(Q, prove, render):
    evaluation = [
        Q(
            "E1",
            "AND evaluates both sides",
            "SELECT a FROM t WHERE b <> 0 AND a / b > 1",
            "handled",
            "Reported: `division by zero`.",
            std="unspecified evaluation order",
            duck="same",
            lean=lambda: prove("SELECT a FROM t WHERE b <> 0 AND a / b > 1", requires=["a >= 0"]),
        ),
        Q(
            "E2",
            "filters are pushed past guards",
            "SELECT a FROM (SELECT * FROM t WHERE b <> 0) WHERE a / b > 1",
            "handled",
            "Reported: conditions are evaluated on `Rel.loose`, the input with filters removed.",
            duck="same",
            lean=lambda: prove(
                "SELECT a FROM (SELECT * FROM t WHERE b <> 0) WHERE a / b > 1",
                requires=["a >= 0"],
            ),
        ),
        Q(
            "E3",
            "numeric CASE is lazy",
            "SELECT CASE WHEN b <> 0 THEN a / b END AS q FROM t",
            "agree",
            "Proved safe, and DataFusion indeed does not fail.",
            duck="same",
            lean=lambda: prove(
                "SELECT CASE WHEN b <> 0 THEN a / b END AS q FROM t",
                requires=["a >= 0"],
            ),
        ),
        Q(
            "E4",
            "boolean CASE becomes AND",
            "SELECT a FROM t WHERE CASE WHEN b <> 0 THEN a / b > 1 ELSE false END",
            "GAP",
            "DataFusion's simplifier turns it into `b <> 0 AND a / b > 1` at run time. `verify` proves it cannot fail; it fails.",
            std="CASE evaluates only the chosen branch",
            duck="same",
            lean=lambda: prove(
                "SELECT a FROM t WHERE CASE WHEN b <> 0 THEN a / b > 1 ELSE false END",
                requires=["a >= 0"],
            ),
        ),
        Q(
            "E5",
            "COALESCE is eager",
            "SELECT coalesce(b, a / b) AS c FROM t",
            "GAP",
            "DataFusion evaluates every argument; Lean's `coalesce` is a CASE, so the division is assumed to happen only where b IS NULL.",
            std="short-circuit (SQL:2003 defines COALESCE as CASE)",
            duck="same",
            lean=lambda: prove("SELECT coalesce(b, a / b) AS c FROM t", requires=["b IS NOT NULL"]),
        ),
    ]
    render([q.run() for q in evaluation])
    return (evaluation,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 8. Substrait round trips and existing workarounds

    `sverify` hands DataFusion's plan to Lean, and in some places runs Lean's
    rewritten plan (`substrait-check --write`) back on DataFusion. Both
    directions have rough edges. None of them is unsound, because the
    failures are loud, but they explain several workarounds in the code:

    * **R1**: DataFusion writes `DISTINCT` (and `UNION`, `INTERSECT`) as an
      aggregate with one *empty* grouping. Its own consumer then rejects that
      plan. Lean reads it as "group by all columns", and its rewrite runs.
    * **R2**: the "spec rename". Substrait renamed `FetchRel.offset`/`count`
      to `offset_expr`/`count_expr`, and DataFusion's protobuf no longer has
      the old fields. Lean's parser reads both, but its writer still emits the
      old ones, so a Lean-written `LIMIT` plan does not load into DataFusion.
      `tests/test_sql.py::written` renames them, and no `sverify` path runs a
      Lean-written `FETCH` on DataFusion.
    * **R3**: Lean writes a `FULL JOIN` as a left join plus an anti join.
      DataFusion's consumer loses table qualifiers at a union, and then
      rejects the plan. For delta plans this is why `Terms.lean` splits plans
      into union-free terms.
    * **R4**: on a zoned timestamp, Lean writes `t + INTERVAL '1 day'` with an
      integer literal, and DataFusion rejects that.
    * **R5**: Ibis compiles integer `a // b` through doubles,
      `CAST(FLOOR(CAST(a AS DOUBLE) / b) AS BIGINT)`, which is wrong beyond
      2^53. `engine.py` replaces it with exact integer arithmetic.
    * **R7**: DataFusion cannot write a `SELECT` without `FROM` as
      Substrait at all ("Producing a row from empty relation is
      unsupported"), so the catalogue's queries all read a table.
    * **R6**: if a table is registered as a PyArrow *dataset*, DataFusion
      pushes filters into PyArrow, which compares doubles by IEEE rules, so
      `v = 'NaN'` stops matching. `put_table` registers record batches
      instead.
    * **R8**: the branches of a `UNION ALL` keep their own nullability (and,
      in a recursive CTE, their own column names), so `SELECT 'x' UNION ALL
      SELECT NULL` returns record batches with different schemas, and
      `to_arrow_table()` fails ("Schema at index 1 was different"). DataFusion
      computes the rows; only collecting them fails. `engine.collect` gives
      the batches one schema, nullable where any branch is.
    """)
    return


@app.cell(hide_code=True)
def _(Q, con, render, run_substrait_json, substrait_json, sv, tables):
    def _df_consumer(sql):
        try:
            run_substrait_json(con, substrait_json(con, sql))
            return "DataFusion reads its own plan"
        except Exception as e:
            return "own plan: error: " + str(e).replace("DataFusion error: ", "")[:60] + "…"

    def _lean_written(sql):
        try:
            rows = run_substrait_json(con, sv.written_plan(substrait_json(con, sql))).to_pylist()
            return f"Lean's rewrite runs on DataFusion: {len(rows)} rows"
        except Exception as e:
            return (
                "Lean's rewrite on DataFusion: error: "
                + str(e).replace("DataFusion error: ", "")[:70]
                + "…"
            )

    def _pyarrow_dataset():
        import datafusion
        import pyarrow.dataset as ds

        ctx = datafusion.SessionContext()
        ctx.register_dataset("fd", ds.dataset(tables["f"]))
        ctx.register_record_batches("fb", [tables["f"].to_batches()])
        q = "SELECT count(*) AS c FROM {} WHERE v = CAST('NaN' AS DOUBLE)"
        d = ctx.sql(q.format("fd")).to_arrow_table().column(0)[0].as_py()
        b = ctx.sql(q.format("fb")).to_arrow_table().column(0)[0].as_py()
        return f"dataset: {d} NaN rows; record batches: {b}"

    roundtrips = [
        Q(
            "R1",
            "DISTINCT as an empty grouping",
            "SELECT DISTINCT x FROM n",
            "handled",
            "Lean parses one empty grouping as all columns and writes a plan DataFusion can read.",
            df=lambda: _df_consumer("SELECT DISTINCT x FROM n"),
            lean=lambda: _lean_written("SELECT DISTINCT x FROM n"),
        ),
        Q(
            "R2",
            "FetchRel offset/count rename",
            "SELECT x FROM n ORDER BY x LIMIT 1",
            "handled",
            "Parser reads both encodings; tests rename the fields Lean writes. Lean-written FETCH plans never run on DataFusion in sverify.",
            df=lambda: _df_consumer("SELECT x FROM n ORDER BY x LIMIT 1"),
            lean=lambda: _lean_written("SELECT x FROM n ORDER BY x LIMIT 1"),
        ),
        Q(
            "R3",
            "FULL JOIN loses qualifiers",
            "SELECT a.x AS l, b.x AS r FROM n a FULL JOIN n b ON a.x = b.x",
            "handled",
            "Fails loudly. Delta plans are split into union-free terms (Terms.lean) for this reason.",
            df=lambda: _df_consumer(
                "SELECT a.x AS l, b.x AS r FROM n a FULL JOIN n b ON a.x = b.x"
            ),
            lean=lambda: _lean_written(
                "SELECT a.x AS l, b.x AS r FROM n a FULL JOIN n b ON a.x = b.x"
            ),
        ),
        Q(
            "R4",
            "zoned timestamp + interval",
            "SELECT t + INTERVAL '1 day' AS d FROM z",
            "handled",
            "Fails loudly on the way back; see T3 for the semantic gap.",
            df=lambda: _df_consumer("SELECT t + INTERVAL '1 day' AS d FROM z"),
            lean=lambda: _lean_written("SELECT t + INTERVAL '1 day' AS d FROM z"),
        ),
        Q(
            "R5",
            "Ibis floor division via doubles",
            "SELECT CAST(FLOOR(CAST(a AS DOUBLE) / b) AS BIGINT) AS ibis, a AS exact FROM big53",
            "handled",
            "engine.py's `_int_floor_divide` compiles `//` to `a / b - 1` when inexact and signs differ.",
            duck="same",
            lean="n/a (the double route is never produced)",
        ),
        Q(
            "R6",
            "PyArrow pushdown uses IEEE",
            "SELECT count(*) FROM f WHERE v = CAST('NaN' AS DOUBLE)",
            "handled",
            "`put_table` registers record batches, never datasets.",
            df=_pyarrow_dataset,
            lean="1 (NaN = NaN)",
        ),
        Q(
            "R7",
            "no plan without FROM",
            "SELECT 1 AS one",
            "handled",
            "DataFusion's producer refuses; nothing reaches Lean.",
            df=lambda: _df_consumer("SELECT 1 AS one"),
        ),
    ]
    render([q.run() for q in roundtrips])
    return (roundtrips,)


@app.cell(hide_code=True)
def _(evaluation, floats, integers, nulls, order, roundtrips, strings, times):
    catalogue = [
        *nulls,
        *floats,
        *integers,
        *strings,
        *times,
        *order,
        *evaluation,
        *roundtrips,
    ]
    return (catalogue,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## What would close the gaps

    * **Missing coercion casts (F6, N7, I11)**: produce Substrait from the
      *analysed* plan, so the casts are explicit. One way is DataFusion's
      `optimized_logical_plan()`, which also applies the CASE-to-AND rewrite
      of E4, so Lean would then see what actually runs. Independently, the
      parser should refuse a comparison or function call whose argument kinds
      differ, instead of evaluating it to NULL.
    * **String comparisons (S6)**: define `BinFn.lt` on strings (by code
      point, like `Value.le`), or refuse `<`/`>` on strings.
    * **Narrow and unsigned integers (I6, I7)**: track the bit width and the
      unsigned type variation in the parser's `Kind`, and check wrap-around
      at that width, or refuse non-64-bit integer arithmetic outright.
      Narrowing casts (I8) are already range-checked (`UnFn.narrow`).
    * **`abs` (I4)**: report `abs(MIN)` as an error, not a wrap.
    * **Boolean `CASE` and `COALESCE` (E4–E5)**: in `Expr.issues`, treat a
      boolean-valued `CASE`, and every `COALESCE`, as evaluating all of its
      branches. That is what DataFusion's simplifier makes of them.
    * **`power(NULL, 0)` (I9)**: either model it (`NULL^0 = 1`) or refuse
      `power` with a constant exponent of 0.
    * **Zoned timestamps (T3)**: refuse interval arithmetic on
      `precisionTimestampTz`.
    * **Doubles a query computes (F1–F3)**: run plans through `sverify`'s
      engines, which canonicalize them, or keep transforms off DataFusion.

    `python/tests/test_datafusion_quirks.py` pins every DataFusion behaviour
    this notebook relies on, so a DataFusion upgrade that changes one of them
    fails the tests. The gaps are pinned as they are today, and each test
    says what a fix should change.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 15. [What is proved, what is trusted](?file=15_trust.py) · [Contents](?file=00_start_here.py) · 17. [One expression, many engines](?file=17_backend_semantics.py) →
    """)
    return


if __name__ == "__main__":
    app.run()

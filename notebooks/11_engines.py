# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "ibis-framework==12.0.0",
#     "marimo",
#     "sverify",
# ]
#
# [tool.uv.sources]
# sverify = { path = "../python", editable = true }
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="medium", app_title="11. Engines and SQL")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 10. [Pipelines](?file=10_pipelines.py) · [Contents](?file=00_start_here.py) · 12. [A complete pipeline](?file=12_fitness.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 11. Engines and SQL

    A proof is about the Lean model. Whether an engine *computes* what the
    model says is a separate question, and engines disagree with each other
    more than you'd think: about NULL join keys, NaN, integer overflow, the
    rounding of integer division, the order of ties. So plans in `sverify`
    come from one producer (the vendored Ibis producer, or DataFusion's for
    SQL strings), but they can **run** on three engines:

    | engine | how the plan runs |
    |:---|:---|
    | `"duckdb"` (default) | `sverify.sql` writes the plan as DuckDB SQL |
    | `"polars"` | `sverify.polars_engine` translates the plan to a Polars `LazyFrame` |
    | `"datafusion"` | DataFusion's own Substrait consumer (the `sverify[datafusion]` extra) |

    Polars and DuckDB run **Lean's written form** of the plan (`sv.written_plan`,
    chapter 2), so what runs is exactly what was checked. Their translators
    don't take engine defaults: they spell out the model's semantics, so
    that disagreements with Lean show up as test failures instead of quiet
    differences.

    ## The same plan on three engines

    Pick a query; each engine runs the same checked plan, next to Lean's
    reference interpreter:
    """)
    return


@app.cell
def _():
    import json

    import ibis
    import sqlglot
    import sverify as sv
    from sverify.testing import canonical, inline_tables, lean_rows

    con = sv.connect()
    sv.create_table(
        con,
        "t",
        ibis.schema({"k": "string", "qty": "int64", "v": "float64"}),
        [("a", 7, 1.5), ("b", -7, float("nan")), (None, 2, 0.0), ("a", 2**63 - 1, None)],
    )
    sv.create_table(
        con,
        "u",
        ibis.schema({"k": "string", "label": "string"}),
        [("a", "alpha"), (None, "nothing"), ("b", "beta")],
    )
    return canonical, con, inline_tables, json, lean_rows, sqlglot, sv


@app.cell(hide_code=True)
def _(con, display, sv):
    display.side_by_side(
        display.table(sv.table_rows(con, "t"), ["k", "qty", "v"], title="t"),
        display.table(sv.table_rows(con, "u"), ["k", "label"], title="u"),
    )
    return


@app.cell(hide_code=True)
def _(mo):
    query = mo.ui.dropdown(
        {
            "join on a key that can be NULL": "select t.k, t.qty, u.label from t join u on t.k = u.k",
            "integer division (truncates)": "select qty, qty / 2 as half, qty % 2 as rest from t where qty < 100",
            "doubles: NaN": "select v, v > 0 as positive, v = 0.0 as is_zero from t",
            "qty + 1 (MAX overflows)": "select qty + 1 as next from t",
        },
        value="join on a key that can be NULL",
        label="query",
    )
    query
    return (query,)


@app.cell(hide_code=True)
def _(canonical, con, display, inline_tables, json, lean_rows, mo, query, sv):
    _plan = sv.substrait_json(con, query.value)
    _written = sv.written_plan(_plan)
    _cols = json.loads(_plan)["relations"][0]["root"]["names"]
    _panels, _results = [], {}
    for _engine in sv.ENGINES:
        try:
            _t = sv.run_plan(con, _written, _engine)
            _results[_engine] = [tuple(r.values()) for r in _t.to_pylist()]
            _panels.append(display.arrow(_t, title=_engine))
        except Exception as _e:
            _panels.append(
                mo.vstack(
                    [
                        mo.md(f"**{_engine}**"),
                        mo.callout(
                            mo.md(f"`{type(_e).__name__}`: {str(_e).splitlines()[0][:120]}"),
                            kind="danger",
                        ),
                    ]
                )
            )
    if " v" not in query.value and "+ 1" not in query.value:  # see "Lean's column" below
        _data = {t: sv.table_rows(con, t) for t in ("t", "u")}
        _lean = lean_rows(json.dumps(inline_tables(json.loads(_plan), _data)))
        _panels.insert(0, display.table(_lean, _cols, title="Lean's Rel.eval"))
    _same = len({repr(canonical(r)) for r in _results.values()}) == 1 and len(_results) == 3
    mo.vstack(
        [
            mo.md(f"```sql\n{query.value}\n```"),
            display.side_by_side(*_panels),
            mo.callout(
                mo.md(
                    "All three engines agree ✓"
                    if _same
                    else "The engines **don't** agree: see below."
                ),
                kind="success" if _same else "warn",
            ),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    What to look for:

    * **NULL join keys** never match (`NULL = NULL` is not TRUE), on every
      engine, because each translator says so explicitly.
    * **Integer division truncates** toward zero, as in DataFusion and Lean
      (`-7 / 2 = -3`). Polars' own `//` floors (`-4`); the translator uses
      truncation instead.
    * **NaN** is one value, equal to itself and above every number, so
      `NaN > 0` is TRUE; and −0.0 is 0.0 (chapter 5), on every engine.
    * **`qty + 1` on the largest integer** is where engines really differ:
      DataFusion silently wraps around to the smallest integer, while the
      Polars and DuckDB translators **raise**, because Lean's integers are
      unbounded and a wrapped result is not the model's answer. That's the
      "may wrap around" warning of chapter 6, made visible.

    **Lean's column** is missing for the last two queries. Values in the
    model are untyped: a double is stored as a very large integer code
    (`SubstraitLean/Float.lean`), so the checker's printer can't tell a
    double from an integer beyond 64 bits, and shows neither faithfully.
    The test suite compares doubles through the engines instead.

    Every contract feature and view can run on another engine:

    ```python
    view = sv.IncrementalView(con, query, "v", engine="polars")

    @sv.transform(ensures=[...], on_unproved="runtime", engine="duckdb")
    def step(orders): ...
    ```

    ## SQL for DuckDB, Snowflake and Spark

    The SQL generator in `sverify.sql` writes a checked plan, or one of
    Lean's update plans, as SQL whose result is `Rel.eval` of the plan.
    Nothing is left to engine defaults: columns are positional (`c0`, `c1`,
    …), filters keep only TRUE rows (`IS TRUE`), integers are checked
    against 64 bits, every `ORDER BY` says where NULLs go. Each engine's
    differences go through a `Dialect`:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    dialect = mo.ui.radio(
        ["duckdb", "snowflake", "spark"], value="duckdb", label="dialect", inline=True
    )
    sql_query = mo.ui.text_area(
        value="select k, qty * 2 as doubled from t where qty > 0",
        label="query over t(k, qty, v)",
        full_width=True,
        rows=2,
    )
    mo.vstack([sql_query, dialect])
    return dialect, sql_query


@app.cell(hide_code=True)
def _(con, dialect, json, mo, sql_query, sqlglot, sv):
    from sverify.sql import Unsupported, to_sql
    from sverify.sql.duckdb import DUCKDB
    from sverify.sql.snowflake import SNOWFLAKE
    from sverify.sql.spark import SPARK

    try:
        _plan = json.loads(sv.substrait_json(con, sql_query.value))
        _dialects = {"duckdb": DUCKDB, "snowflake": SNOWFLAKE, "spark": SPARK}
        _sql = to_sql(_plan, _dialects[dialect.value])
        _pretty = sqlglot.transpile(_sql, read=dialect.value, pretty=True)[0]
        _out = mo.md(f"```sql\n{_pretty}\n```")
    except Unsupported as _e:
        _out = mo.callout(mo.md(f"**Unsupported** in {dialect.value}: {_e}"), kind="warn")
    except Exception as _e:
        _out = mo.callout(mo.md(f"`{_e}`"), kind="danger")
    _out
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Long, but every line is there for a reason. Try
    `select k, row_number() over (partition by k order by qty) as rn from t`
    in each dialect: DuckDB gets an ordinal column so ties break the way
    Lean's stable sort breaks them, while **Snowflake and Spark refuse**,
    because their tables have no row order to break ties with. If a contract report says
    `deterministic` (chapter 7), pass `tie_free=True` to promise there are
    no ties.

    Snowflake-specific choices: integers are `NUMBER(38,0)` checked against
    the 64-bit range, timestamps `TIMESTAMP_NTZ(6)`, every identifier quoted.
    Where Snowflake can't match the model, the query raises or is refused
    instead of answering differently, as for interval-valued expressions
    (Snowflake has no interval type).

    ## Spark and Databricks

    The Spark dialect (`sverify.sql.spark`) targets Spark 4 and Databricks
    SQL. It assumes the session settings of `SPARK_CONF`, above all
    `spark.sql.ansi.enabled`: without ANSI mode an overflow wraps around and
    a bad cast is NULL. Spark answers several of
    [chapter 15](?file=15_backend_semantics.py)'s questions its own way, and
    each is spelled out or refused:

    * `/` of integers is a double, so division is `div`; `/` of doubles
      raises on a zero divisor in ANSI mode, so `x / 0.0` is written as the
      IEEE ±inf or NaN.
    * `CAST(9.3e18 AS BIGINT)` saturates instead of raising, and `FLOOR`
      and `CEIL` return integers: each is checked or repaired.
    * `SUM` of `BIGINT` raises on an overflowing partial sum, though Lean's
      total may fit: it adds `DECIMAL(38,0)` instead.
    * `TIMESTAMP` is the session time zone's (`TIMESTAMP_LTZ`), and so is
      what `date_trunc` returns: the SQL stays in `TIMESTAMP_NTZ`.
    * `POWER` of doubles is Java's `Math.pow` (within 1 ulp of C's), so it
      is refused, as are sorts and windows over a table without
      `tie_free=True`. Over `VALUES`, a `SUM` of doubles adds in Lean's
      order (`aggregate` over the sorted list).

    Unlike Snowflake, Spark runs locally: the tests run every coverage case
    and every query of the Snowflake suite on a local Spark session and
    compare them with `Rel.eval`. DataFusion's own departures from the model
    are in [chapter 14](?file=14_datafusion_semantics.py).

    ## Testing the engines against the model

    The Lean evaluator is the specification. The test suite runs every
    fixture and every update plan on DataFusion, Polars and DuckDB with
    random tables and compares them with each other and with `Rel.eval`, row
    for row in Lean's order where order matters (`LIMIT`, windows). The
    Snowflake SQL is checked by parsing and by running it on
    [fakesnow](https://github.com/tekumara/fakesnow), a Snowflake emulator,
    or on a real account if you configure one.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 10. [Pipelines](?file=10_pipelines.py) · [Contents](?file=00_start_here.py) · 12. [A complete pipeline](?file=12_fitness.py) →
    """)
    return


if __name__ == "__main__":
    app.run()

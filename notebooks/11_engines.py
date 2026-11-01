# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "ibis-framework==12.0.0",
#     "marimo",
#     "sqlglot==30.27.0",
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
    ← 10. [Pipelines](?file=10_pipelines.py) · [Contents](?file=00_start_here.py) · 12. [Doubles, time and text](?file=12_values.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 11. Engines and SQL

    Say your pipeline was proved and tested on DuckDB on your laptop, and
    the platform team wants it on Spark next quarter. The proof hasn't
    changed, but will the answers?

    A proof is about the Lean model. Whether an engine *computes* what the
    model says is a separate question, and engines disagree with each other
    more than you'd think: about NULL join keys, NaN, integer overflow, the
    rounding of integer division, the order of ties. So plans in `sverify`
    come from one producer (the vendored Ibis producer, or DataFusion's for
    SQL strings), but they can **run** on three engines in process
    (`sverify.engines.ENGINES`), and on Spark:

    | engine | how the plan runs |
    |:---|:---|
    | `"duckdb"` (default) | the SQL generator (`sverify.engines.to_sql`) writes the plan as DuckDB SQL |
    | `"polars"` | a translator turns the plan into a Polars `LazyFrame` |
    | `"datafusion"` | DataFusion's own Substrait consumer (the `sverify[datafusion]` extra) |
    | `"spark"`, or a Spark session | the SQL generator writes Spark SQL (the `sverify[spark]` extra; below) |

    Polars and DuckDB run **Lean's written form** of the plan
    (`sverify.engines.written_plan`, chapter 14), so what runs is exactly
    what was checked. Their translators
    don't take engine defaults: they spell out the model's semantics, so
    that disagreements with Lean show up as test failures instead of quiet
    differences.

    ## The same plan on three engines

    We'll line them up. Pick a query; each engine runs the same checked
    plan (`sverify.engines.run(con, plan, engine)`), next to Lean's
    reference interpreter:
    """)
    return


@app.cell
def _():
    import json

    import ibis
    import sqlglot
    import sverify as sv
    from sverify.engines import ENGINES, create_table, run, substrait_json, table_rows, written_plan

    T_SCHEMA = ibis.schema({"k": "string", "qty": "int64", "v": "float64"})
    U_SCHEMA = ibis.schema({"k": "string", "label": "string"})
    T_ROWS = [("a", 7, 1.5), ("b", -7, float("nan")), (None, 2, 0.0), ("a", 2**63 - 1, None)]
    U_ROWS = [("a", "alpha"), (None, "nothing"), ("b", "beta")]

    con = sv.connect()
    create_table(con, "t", T_SCHEMA, T_ROWS)
    create_table(con, "u", U_SCHEMA, U_ROWS)
    return (
        ENGINES,
        T_ROWS,
        T_SCHEMA,
        U_ROWS,
        U_SCHEMA,
        con,
        json,
        run,
        sqlglot,
        substrait_json,
        sv,
        table_rows,
        written_plan,
    )


@app.cell(hide_code=True)
def _(con, display, table_rows):
    display.side_by_side(
        display.table(table_rows(con, "t"), ["k", "qty", "v"], title="t"),
        display.table(table_rows(con, "u"), ["k", "label"], title="u"),
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
def _(ENGINES, con, display, json, mo, query, run, substrait_json, table_rows, written_plan):
    from sverify.testing import canonical, inline_tables, lean_rows

    _plan = substrait_json(con, query.value)
    _written = written_plan(_plan)
    _cols = json.loads(_plan)["relations"][0]["root"]["names"]
    _panels, _results = [], {}
    for _engine in ENGINES:
        try:
            _t = run(con, _written, _engine)
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
        _data = {t: table_rows(con, t) for t in ("t", "u")}
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
      `NaN > 0` is TRUE; and −0.0 is 0.0 (chapter 12), on every engine.
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

    ## Choosing the engine for a node

    A node (chapters 9 and 10) doesn't fix its engine when you build it:
    the plan is the same everywhere, and you pick where it runs each time
    you refresh, with `node.refresh(engine="polars")`, `"datafusion"`,
    `"spark"` or a Spark session (DuckDB in memory is the default). We'll
    build the NULL-key join as a transform over `t` and `u` and refresh a
    fresh node on each engine:
    """)
    return


@app.cell
def _(ENGINES, T_ROWS, T_SCHEMA, U_ROWS, U_SCHEMA, sv):
    import pyarrow as _pa
    from sverify.io import StaticSource

    def _source(schema, rows, name):
        _arrow = schema.to_pyarrow()
        return StaticSource(
            _pa.Table.from_pylist([dict(zip(_arrow.names, r)) for r in rows], schema=_arrow),
            name=name,
        )

    _t, _u = _source(T_SCHEMA, T_ROWS, "t"), _source(U_SCHEMA, U_ROWS, "u")

    @sv.transform()
    def labelled(t, u):
        return t.join(u, t.k == u.k).select(t.k, t.qty, u.label)

    by_engine = {}
    for _engine in ENGINES:
        _node = _t.pipe(labelled, u=_u)
        _node.refresh(engine=_engine)
        by_engine[_engine] = sorted(tuple(r.values()) for r in _node.to_arrow().to_pylist())
    by_engine
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The same rows on every engine, and the NULL key matches nothing. A node
    keeps its state between refreshes, so the next refresh may use another
    engine than the last one. Contracts checked on the data can name an
    engine too:

    ```python
    node.refresh(engine="polars")   # or "datafusion", "spark", a SparkSession

    @sv.transform(ensures=[...], on_unproved="runtime", engine="duckdb")
    def step(orders): ...
    ```

    ## SQL for DuckDB, Snowflake and Spark

    Often the data already lives in a warehouse, and the plan has to go to
    it rather than the other way round. The SQL generator,
    `sverify.engines.to_sql`, writes a checked plan, or one of Lean's update plans, as SQL whose
    result is `Rel.eval` of the plan. Nothing is left to engine defaults:
    columns are positional (`c0`, `c1`, …), filters keep only TRUE rows (`IS
    TRUE`), integers are checked against 64 bits, every `ORDER BY` says
    where NULLs go. Each engine's differences go through a `Dialect`:
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
def _(con, dialect, json, mo, sql_query, sqlglot, substrait_json):
    from sverify.engines import DUCKDB, SNOWFLAKE, SPARK, Unsupported, to_sql

    try:
        _plan = json.loads(substrait_json(con, sql_query.value))
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
    because their tables have no row order to break ties with. If a
    contract report says `deterministic` (chapter 7), pass `tie_free=True`
    to promise there are no ties.

    Snowflake-specific choices: integers are `NUMBER(38,0)` checked against
    the 64-bit range, timestamps `TIMESTAMP_NTZ(6)`, intervals counts of
    microseconds (Snowflake has no interval type), every identifier quoted.
    Where Snowflake can't match the model, the query raises or is refused
    instead of answering differently, as for an interval-valued result
    column.

    ## Spark and Databricks

    The Spark dialect (`sverify.engines.SPARK`) targets Spark 4 and
    Databricks SQL; it is also what `node.refresh(engine="spark")` runs. It
    assumes the session settings of `sverify.engines.SPARK_CONF`, above all
    `spark.sql.ansi.enabled`: without ANSI mode an overflow wraps around and
    a bad cast is NULL. Spark answers several of
    [chapter 17](?file=17_backend_semantics.py)'s questions its own way, and
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
    are in [chapter 16](?file=16_datafusion_semantics.py).

    ## Testing the engines against the model

    Moving a pipeline to another engine is only safe if every engine gives
    the model's answer. The Lean evaluator is the specification. The test
    suite runs every fixture and every update plan on DataFusion, Polars and
    DuckDB with random tables and compares them with each other and with
    `Rel.eval`, row for row in Lean's order where order matters (`LIMIT`,
    windows). The Snowflake SQL is checked by parsing and by running it on
    [fakesnow](https://github.com/tekumara/fakesnow), a Snowflake emulator,
    or on a real account if you configure one.

    You can now run a checked plan, or refresh a node, on DuckDB, Polars,
    DataFusion or Spark, or hand it to Snowflake as SQL, and you know where an engine could
    depart from the model: the translators and the SQL generator spell out
    the model's semantics and raise or refuse rather than answer
    differently, and the tests compare the engines with `Rel.eval`. That
    ends the tour of what you can build. Chapter 12,
    [Doubles, time and text](?file=12_values.py), starts the reference and
    deep-dive part, with how the model treats the values themselves.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 10. [Pipelines](?file=10_pipelines.py) · [Contents](?file=00_start_here.py) · 12. [Doubles, time and text](?file=12_values.py) →
    """)
    return


if __name__ == "__main__":
    app.run()

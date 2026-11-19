# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "ibis-framework==12.0.0",
#     "marimo",
#     "sverify[duckdb,polars,spark]",
# ]
#
# [tool.uv.sources]
# sverify = { path = "../python", editable = true }
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="compact", app_title="7. Engines")


@app.cell(hide_code=True)
def _():
    import os
    import shutil

    import ibis
    import marimo as mo
    import sqlglot
    import sverify as sv
    from sverify import display

    # Spark runs in a JVM; without one its cells are skipped (a molab sandbox, say).
    SPARK = shutil.which("java") is not None or bool(os.environ.get("JAVA_HOME"))
    return SPARK, display, ibis, mo, sqlglot, sv


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 6. [Running it in production](?file=06_running_in_production.py)
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 7. Engines

    Say your team's rollup runs in three places. Analysts try it on DuckDB
    in a notebook, the service that serves it runs Polars, and the warehouse
    that stores the history runs Spark. The proof was made once, on one
    plan. Nobody wants to redo it for each engine, and nobody wants to
    find out at 3 a.m. which engine reads a plan differently.

    We'll prove one query, run it on DuckDB, Polars and Spark, write it as
    SQL for Spark and Snowflake, and then ask an engine for something it
    can't run. Each refusal names an exit, and we'll follow them.

    ## 1. One query, proved once

    We total each customer's order quantities. A sum of integers can
    overflow, so the verdict may come with checks that the run makes on the
    data, and it says so:
    """)
    return


@app.cell
def _(ibis, sv):
    con = sv.connect()
    con.create(
        "orders",
        ibis.schema({"customer": "string", "item": "string", "qty": "int64"}),
        [
            ("ada", "tea", 3),
            ("bo", "tea", 4),
            ("ada", "cake", 5),
            ("bo", "milk", 1),
            ("cy", "tea", 2),
        ],
    )
    _orders = con.table("orders")
    rollup = sv.verify(
        _orders.group_by(_orders.customer).aggregate(
            total=_orders.qty.sum(), lines=_orders.qty.count()
        )
    )
    rollup.verdict
    return con, rollup


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 2. Run it where your data lives

    `report.run(con, engine, route="auto")` runs the checked plan on an
    engine. Before it runs, `route="auto"` asks how the proof reaches that
    engine: the plan's class there is `exact` (every result the engine can
    give, the reference allows), `observed`, `shim` (the plan is rewritten by
    a proved translation first) or `refused`. We run the rollup on each of
    the three:
    """)
    return


@app.cell
def _(SPARK, con, display, mo, rollup):
    results = {}
    for _engine in ["duckdb", "polars", *(["spark"] if SPARK else [])]:
        _table = rollup.run(con, _engine, route="auto")
        results[_engine] = sorted(tuple(r.values()) for r in _table.to_pylist())
    mo.vstack(
        [
            display.side_by_side(
                *(
                    display.table(rows, ["customer", "total", "lines"], title=name)
                    for name, rows in results.items()
                )
            ),
            *(
                []
                if SPARK
                else [mo.md("Spark needs Java, and none is installed here: its run is skipped.")]
            ),
        ]
    )
    return (results,)


@app.cell(hide_code=True)
def _(mo, results):
    mo.md(f"""
    All {len(results)} agree, and the plan didn't change between them. What differs
    is how each engine reaches the proof:
    """)
    return


@app.cell
def _(results, rollup):
    {engine: rollup.routes[engine].cls for engine in results}
    return


@app.cell(hide_code=True)
def _(SPARK, mo):
    _spark = (
        "Spark adds integers in a wider decimal and checks the result fits again, and Polars"
        if SPARK
        else "Polars"
    )
    mo.md(f"""
    DuckDB gives what the reference gives, `exact`. {"Polars and Spark need a shim" if SPARK else "Polars needs a shim"}:
    {_spark} writes the sum of no rows as NULL. Each shim carries its own
    proof or test evidence, and the route says which.

    ## 3. The same plan as SQL

    A warehouse runs SQL. `report.to_sql(dialect)`
    writes the checked plan for DuckDB, Spark or Snowflake. Spark's version
    keeps the overflow check of the sum, raising an error where the sum
    leaves 64 bits:
    """)
    return


@app.cell
def _(mo, rollup, sqlglot):
    _sql = sqlglot.parse_one(rollup.to_sql("spark"), read="spark").sql(dialect="spark", pretty=True)
    mo.md(f"```sql\n{_sql}\n```")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 4. A refusal names its exit

    An engine runs only what Lean can say it computes. Ask for a plan it
    can't run, and Sverify says what to do. We number each
    customer's lines, with no order stated:
    """)
    return


@app.cell
def _(con, ibis, sv):
    _orders = con.table("orders")
    numbered = sv.verify(
        _orders.select(
            _orders.customer,
            line=ibis.row_number().over(group_by=_orders.customer),
        )
    )
    try:
        numbered.to_sql("spark")  # the writer refuses, with no JVM involved
    except Exception as _e:
        print(f"{type(_e).__name__}: {_e}")
    return (numbered,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Spark's window functions need an `ORDER BY` here, and the plan states
    none. The message offers one exit: `engine='duckdb'` runs the plan on
    the engine that numbers rows without one, in the order it happens to
    find them:
    """)
    return


@app.cell
def _(con, numbered):
    numbered.run(con, "duckdb", route="auto").to_pylist()
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The plan can also say the order itself. A window with an `ORDER BY` runs
    on every engine:
    """)
    return


@app.cell
def _(SPARK, con, ibis, sv):
    _orders = con.table("orders")
    ordered = sv.verify(
        _orders.select(
            _orders.customer,
            _orders.item,
            line=ibis.row_number().over(group_by=_orders.customer, order_by=_orders.item),
        )
    )
    {
        _engine: sorted(
            tuple(r.values()) for r in ordered.run(con, _engine, route="auto").to_pylist()
        )
        for _engine in ["duckdb", "polars", *(["spark"] if SPARK else [])]
    }
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Some refusals name a rewrite as their exit. Spark and Snowflake take
    their `ln` from Java's `StrictMath` and an undocumented libm, and Lean's
    model uses C's. The writer refuses the step and says so:
    """)
    return


@app.cell
def _(con, sv):
    _orders = con.table("orders")
    logged = sv.verify(_orders.filter(_orders.qty > 0).select(_orders.customer, y=_orders.qty.ln()))
    for _dialect in ["spark", "snowflake"]:
        try:
            logged.to_sql(_dialect)
        except Exception as _e:
            print(f"{_dialect}: {type(_e).__name__}: {_e}")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    A refusal of an engine or a writer names its exit: run the plan on
    DuckDB, or rewrite the step. The
    [engines page](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/stability.md#engines)
    says which engine runs what, and why.

    You can now prove a query once and run it on DuckDB, Polars or Spark,
    hand the same plan to a warehouse as SQL, and read a refusal as
    directions. The last chapter,
    [Your dbt project](?file=08_dbt.py), proves the tests of a dbt project
    before its models run. The
    [guide](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/guide.md)
    covers every feature in more detail.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 6. [Running it in production](?file=06_running_in_production.py) · 8. [Your dbt project](?file=08_dbt.py) →
    """)
    return


if __name__ == "__main__":
    app.run()

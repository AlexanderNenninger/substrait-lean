# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "deltalake",
#     "duckdb",
#     "ibis-framework==12.0.0",
#     "marimo",
#     "sverify[datafusion,polars,delta]",
# ]
#
# [tool.uv.sources]
# sverify = { path = "../python", editable = true }
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="compact", app_title="3. An orders mart")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 2. [Sensor alerts](?file=02_sensor_alerts.py) · 4. [Contracts](?file=04_contracts.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 3. An orders mart: dbt tests, proved

    Say you own the dashboard the sales team opens every morning:
    revenue per city and day. The regional managers' bonuses depend on it,
    so when a number is off, you hear about it before lunch.

    It's a mart model of the kind most analytics teams have, with one
    subtlety: the city is the customer's city when the order was placed.
    Customers move, so the city comes from a type-2 slowly changing
    dimension (dbt snapshots build these), and the join is a point-in-time
    join (`dbt-scd2-point-in-time` in the
    [query catalogue](../catalogue/INDEX.md)).

    In dbt this model would come with tests: `not_null(city)`,
    `unique(city, day)`, `revenue >= 0`. They run after the model is built,
    on the data that happens to be there. Here they are the model's
    contract, proved for every possible input before it runs, and one of
    them fails for a reason the test data doesn't show. We'd rather see that
    failure here than in a regional manager's inbox.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 1. The sources: two Delta tables

    `customer_history` has one row per customer and version: `[valid_from,
    valid_to)`, with `valid_to` NULL for the current one. Customer 1 moved
    from Paris to Lyon on 2 May, and their later orders count for Lyon.
    """)
    return


@app.cell
def _():
    import datetime as dt
    import tempfile
    from pathlib import Path

    import ibis
    import pyarrow as pa
    import sverify as sv
    from deltalake import DeltaTable, write_deltalake
    from sverify.engines import ENGINES, SNOWFLAKE, SPARK, to_sql
    from sverify.io import DeltaSink, DeltaSource

    lake = Path(tempfile.mkdtemp())

    ORDERS = pa.schema(
        [
            pa.field("order_id", pa.int64(), nullable=False),
            pa.field("customer_id", pa.int64(), nullable=False),
            pa.field("order_ts", pa.timestamp("us"), nullable=False),
            pa.field("amount_cents", pa.int64(), nullable=False),
        ]
    )
    HISTORY = pa.schema(
        [
            pa.field("customer_id", pa.int64(), nullable=False),
            pa.field("city", pa.string(), nullable=False),
            pa.field("valid_from", pa.timestamp("us"), nullable=False),
            pa.field("valid_to", pa.timestamp("us")),
        ]
    )

    def may(day, hour=12):
        return dt.datetime(2026, 5, day, hour)

    def rows(schema, *rs):
        return pa.Table.from_pylist(
            [dict(zip(schema.names, r, strict=True)) for r in rs], schema=schema
        )

    _cdf = {"delta.enableChangeDataFeed": "true"}
    orders_v0 = rows(
        ORDERS,
        (1, 1, may(1), 1200),
        (2, 1, may(3), 800),
        (3, 2, may(3), 4599),
        (4, 2, may(3, 18), 100),
        (5, 3, may(4), 999),
    )
    history_v0 = rows(
        HISTORY,
        (1, "Paris", may(1, 0), may(2, 0)),
        (1, "Lyon", may(2, 0), None),
        (2, "Rome", may(1, 0), None),
        (3, "Oslo", may(1, 0), None),
    )
    write_deltalake(lake / "orders", orders_v0, configuration=_cdf)
    DeltaTable(lake / "orders").alter.add_constraint({"non_negative": "amount_cents >= 0"})
    write_deltalake(lake / "customer_history", history_v0, configuration=_cdf)
    return (
        DeltaSink,
        DeltaSource,
        DeltaTable,
        ENGINES,
        HISTORY,
        ORDERS,
        SNOWFLAKE,
        SPARK,
        dt,
        history_v0,
        ibis,
        lake,
        may,
        orders_v0,
        rows,
        sv,
        to_sql,
        write_deltalake,
    )


@app.cell(hide_code=True)
def _(display, history_v0, orders_v0):
    display.side_by_side(
        display.arrow(orders_v0, title="orders"),
        display.arrow(history_v0, title="customer_history"),
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 2. The model, and its tests as a contract

    The join takes the history row whose range contains the order time.
    The ranges are half-open, so an order at the instant of a move gets the
    new city, and the current row's NULL `valid_to` means "still valid".
    The catalogue lists both as pitfalls of this query.
    """)
    return


@app.cell
def _(dt, sv):
    from ibis import _

    def city_day_revenue(orders, history, unknown_city=None):
        h = history
        joined = orders.left_join(
            h,
            (orders.customer_id == h.customer_id)
            & (h.valid_from <= orders.order_ts)
            & (h.valid_to.isnull() | (orders.order_ts < h.valid_to)),
        )
        city = h.city if unknown_city is None else h.city.fill_null(unknown_city)
        return (
            joined.select(
                city=city, day=orders.order_ts.truncate("D"), amount_cents=orders.amount_cents
            )
            .group_by(["city", "day"])
            .aggregate(n_orders=_.count(), revenue_cents=_.amount_cents.sum())
            .mutate(revenue_cents=_.revenue_cents.fill_null(0))
        )

    REQUIRES = {
        "orders": [
            sv.unique("order_id"),
            _.amount_cents >= 0,
            _.order_ts >= dt.datetime(2000, 1, 1),
        ]
    }
    ENSURES = [  # the dbt tests
        _.city.notnull(),
        _.day.notnull(),
        sv.unique("city", "day"),
        _.revenue_cents >= 0,
    ]
    return ENSURES, REQUIRES, city_day_revenue


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    We check the first version, where `city` is the dimension's column
    as it is:
    """)
    return


@app.cell
def _(ENSURES, HISTORY, ORDERS, REQUIRES, city_day_revenue, ibis, sv):
    orders_t = ibis.table(ibis.Schema.from_pyarrow(ORDERS), name="orders")
    history_t = ibis.table(ibis.Schema.from_pyarrow(HISTORY), name="history")
    first_try = sv.verify(city_day_revenue(orders_t, history_t), requires=REQUIRES, ensures=ENSURES)
    assert [c.label for c in first_try.unproved] == ["_.city.notnull()"]
    return first_try, history_t, orders_t


@app.cell(hide_code=True)
def _(first_try, mo):
    mo.md(first_try._repr_markdown_())
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    `not_null(city)` is refused, although `city` is NOT NULL in the
    dimension and every order in the sample data has a city. The checker
    knows what the data doesn't show: an order whose customer has no history
    row yet (a new customer whose snapshot hasn't run), or one placed before
    the customer's first `valid_from`, matches nothing in the left join, and
    its city is NULL. That is dbt's `relationships` test failing in
    production after passing in CI.

    The other tests are proved. The grouping columns are a key of an
    aggregate's output, `revenue_cents >= 0` follows from the precondition
    on amounts (and the `fill_null` for an empty sum), and `day` is never
    NULL because `order_ts` isn't. The report assumes that each city's daily
    `SUM` fits 64 bits, since no contract can bound how many orders a group
    holds, and the job checks the sums while it runs. The hint names the
    bound and the row cap (`sv.max_rows`) that would prove it instead.

    Someone has to decide what such an order counts as, and the dashboard's
    readers would rather see an `unknown` row than revenue that vanished. So
    we say it:
    """)
    return


@app.cell
def _(ENSURES, REQUIRES, city_day_revenue, sv):
    @sv.transform(requires=REQUIRES, ensures=ENSURES)
    def daily_city_revenue(orders, history):
        return city_day_revenue(orders, history, unknown_city="unknown")

    return (daily_city_revenue,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### The same model in SQL

    If your team writes models in SQL, `sv.verify` checks the SQL text
    against the same kind of contract, with conditions as SQL snippets. The
    SQL is DuckDB's dialect, which sverify plans with its own SQLGlot lift.
    It needs `coalesce` around the `SUM` for the reason the Ibis version
    needs `fill_null`:
    """)
    return


@app.cell
def _(history_t, orders_t, sv):
    MODEL_SQL = """
    select coalesce(h.city, 'unknown') as city,
           date_trunc('day', o.order_ts) as day,
           count(*) as n_orders,
           coalesce(sum(o.amount_cents), 0) as revenue_cents
    from orders o
    left join history h
      on o.customer_id = h.customer_id
     and h.valid_from <= o.order_ts
     and (h.valid_to is null or o.order_ts < h.valid_to)
    group by coalesce(h.city, 'unknown'), date_trunc('day', o.order_ts)
    """
    sql_report = sv.verify(
        MODEL_SQL,
        tables={"orders": orders_t, "history": history_t},
        requires={"orders": ["amount_cents >= 0", sv.unique("order_id")]},
        ensures=["city is not null", "revenue_cents >= 0", sv.unique("city", "day")],
    )
    assert all(c.proved for c in sql_report.ensures)
    print(sql_report)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The job below uses the Ibis version, because nodes are built from
    transforms and contracts travel from one step to the next through them.

    ## 3. Build it from the Delta tables

    Now we wire it up. The model reads both tables as sources, and piping
    them into it builds a node. A left join and an aggregate have no proved
    delta rules yet, so the node is recomputed on each refresh, and its
    status says so:
    """)
    return


@app.cell
def _(DeltaSource, daily_city_revenue, lake):
    orders = DeltaSource(str(lake / "orders"))
    history = DeltaSource(str(lake / "customer_history"), name="history")
    mart = orders.pipe(daily_city_revenue, history=history)
    assert daily_city_revenue.report.proved
    mart.refresh()
    print(mart.status())
    return history, mart, orders


@app.cell(hide_code=True)
def _(display, mart):
    display.arrow(
        mart.to_arrow().sort_by([("city", "ascending"), ("day", "ascending")]),
        title="daily_city_revenue",
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Paris on 1 May, Lyon on 3 May: customer 1's orders follow the move.

    ## 4. Same answer on every engine

    The same SQL text means different things on different engines. Suppose
    someone adds an average order value as `revenue_cents / n_orders`:
    """)
    return


@app.cell
def _():
    import datafusion
    import duckdb

    {
        "DuckDB": duckdb.sql("select 4699 / 2 as avg").fetchall()[0][0],
        "DataFusion": datafusion.SessionContext()
        .sql("select 4699 / 2 as avg")
        .to_pylist()[0]["avg"],
    }
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    DuckDB's `/` on integers gives a double, DataFusion's (and
    PostgreSQL's) truncates, Snowflake's gives a NUMBER with extra decimals,
    and Spark's gives a double. A model moved from DuckDB in development to
    Snowflake in production changes its numbers without an error, and
    whoever reconciles the dashboard with finance notices first. Sverify's
    translations write out what the plan means (integer division truncates
    on every engine), so the checked plan gives the same rows on each,
    whichever `engine=` the node is refreshed with. DuckDB is the reference
    engine (Tier 1); see the
    [engine tiers](https://github.com/AlexanderNenninger/substrait-lean/blob/main/python/README.md)
    for the others:
    """)
    return


@app.cell
def _(ENGINES, SNOWFLAKE, SPARK, daily_city_revenue, history, mart, orders, to_sql):
    _results = {}
    for _engine in ENGINES:
        _node = orders.pipe(daily_city_revenue, history=history)
        _node.refresh(engine=_engine)
        _results[_engine] = sorted(map(repr, _node.to_arrow().to_pylist()))
    assert len({repr(r) for r in _results.values()}) == 1
    {
        "engines that agree": list(_results),
        "Snowflake SQL": f"{len(to_sql(mart.internal_plan, SNOWFLAKE))} characters",
        "Spark SQL": f"{len(to_sql(mart.internal_plan, SPARK))} characters",
    }
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 5. The next day: a move and a new customer

    Overnight, the snapshot job records that customer 2 moved from Rome to
    Milan at 15:00 on 3 May: it closes the old row and adds a new one. A new
    customer, 4, places an order before their first snapshot.

    Before the changes land, we store the mart in a Delta table with
    `.write`. Its first refresh creates the table.
    """)
    return


@app.cell
def _(DeltaSink, DeltaTable, HISTORY, ORDERS, lake, mart, may, rows, write_deltalake):
    stored = mart.write(DeltaSink(str(lake / "daily_city_revenue")))
    print(stored.refresh())

    _h = DeltaTable(lake / "customer_history")
    _h.update(
        updates={"valid_to": "'2026-05-03 15:00:00'"},
        predicate="customer_id = 2 AND valid_to IS NULL",
    )
    write_deltalake(_h, rows(HISTORY, (2, "Milan", may(3, 15), None)), mode="append")
    write_deltalake(lake / "orders", rows(ORDERS, (6, 4, may(4), 500)), mode="append")
    return (stored,)


@app.cell
def _(stored):
    print(stored.refresh())
    _rows = stored.to_arrow().to_pylist()
    assert ("Milan", 1, 100) in [(r["city"], r["n_orders"], r["revenue_cents"]) for r in _rows]
    assert "unknown" in [r["city"] for r in _rows]
    return


@app.cell(hide_code=True)
def _(display, mo, stored):
    mo.vstack(
        [
            display.arrow(
                stored.to_arrow().sort_by([("city", "ascending"), ("day", "ascending")]),
                title="daily_city_revenue",
            ),
            mo.md(
                "Order 4 (18:00 on 3 May) moved from Rome to Milan, and customer 4's order "
                "is counted under `unknown`, so it neither disappears nor makes `city` NULL. "
                "The sink merged the change in one commit; its NOT NULL and CHECK constraints "
                "are the proved tests."
            ),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## What you got

    You now have a dashboard model whose dbt tests are a contract, proved
    before the model runs. The one that would have failed in production,
    `not_null(city)` after a left join, failed at definition time instead.
    The preconditions came from Delta metadata where possible, and the
    checked plan gives the same rows on DuckDB, Polars and DataFusion, and
    can be written as Snowflake or Spark SQL, where the same SQL text would
    not. The model is outside the incremental fragment, so it runs as a node
    that is recomputed and diffed, with its sink merged exactly once per
    state.

    Next up: [Contracts](?file=04_contracts.py) explains what Lean tracks
    and how contracts compose, and
    [Pipelines and engines](?file=05_pipelines_and_engines.py) covers
    nodes, sinks, incremental maintenance and the engines.
    """)
    return


if __name__ == "__main__":
    app.run()

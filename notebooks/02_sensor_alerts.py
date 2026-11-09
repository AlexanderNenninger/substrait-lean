# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "duckdb",
#     "ibis-framework==12.0.0",
#     "marimo",
#     "pyiceberg[sql-sqlite]",
#     "sverify[polars,iceberg]",
# ]
#
# [tool.uv.sources]
# sverify = { path = "../python", editable = true }
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="compact", app_title="2. Sensor alerts")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 1. [Duplicate card payments](?file=01_duplicate_payments.py) · 3. [An orders mart](?file=03_orders_mart.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 2. Sensor alerts from an Iceberg table

    Say you look after a plant's temperature sensors. When a machine runs
    hot for three minutes in a row, someone on call gets paged, and if the
    alert is wrong in either direction, it's their night or the machine
    that pays for it. You want an alert at every reading that is the third
    or more in a row above 30 °C.

    The sensors write a reading per device per minute to an Iceberg table,
    and the rule is `iot-consecutive-threshold` in the
    [query catalogue](../catalogue/INDEX.md) (Azure Stream Analytics'
    `MATCH_RECOGNIZE` example). In SQL that is two `LAG`s over a window.
    Window queries are where engines disagree, and we'll run into three
    causes:

    * ties: two readings of a device at the same instant make "previous
      reading" ambiguous, and each engine picks one;
    * NaN: a glitching sensor sends NaN. In SQL `NaN > 30` is TRUE, because
      NaN sorts above every number, and in Python and pandas it is False, so
      a prototype and the production job disagree;
    * warehouses without row order: Snowflake and Spark tables have no order
      to break ties with.

    As in the [first notebook](?file=01_duplicate_payments.py), the job
    reads the source, states and proves a contract, runs on several engines,
    keeps up with new data and writes a sink.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 1. The source: an Iceberg table of readings

    Iceberg needs a catalog, so a small SQLite one in a temporary folder
    stands in for Glue, a REST catalog or Unity. `device_id` and `ts` are
    `required`. Device 2 skipped a reading (NULL), and device 3 had a glitch
    and sent NaN. We'll see what each does to the alerts.
    """)
    return


@app.cell
def _():
    import datetime as dt
    import tempfile
    import warnings

    import ibis
    import pyarrow as pa
    import sverify as sv
    from pyiceberg.catalog.sql import SqlCatalog
    from sverify.engines import ENGINES, UnsupportedError, to_sql
    from sverify.errors import PreconditionError
    from sverify.io import IcebergSink, IcebergSource

    warnings.filterwarnings("ignore", module="pyiceberg")
    _dir = tempfile.mkdtemp()
    catalog = SqlCatalog("lake", uri=f"sqlite:///{_dir}/catalog.db", warehouse=f"file://{_dir}")
    catalog.create_namespace("plant")

    READING = pa.schema(
        [
            pa.field("device_id", pa.int64(), nullable=False),
            pa.field("ts", pa.timestamp("us"), nullable=False),
            pa.field("temperature", pa.float64()),
        ]
    )

    def minute(m):
        return dt.datetime(2026, 7, 1, 12, m)

    def readings_batch(*rows):
        return pa.Table.from_pylist(
            [dict(zip(READING.names, r, strict=True)) for r in rows], schema=READING
        )

    first = readings_batch(
        (1, minute(0), 29.5),
        (1, minute(1), 31.0),
        (1, minute(2), 32.5),
        (1, minute(3), 33.0),  # third high reading in a row: alert
        (2, minute(0), 35.0),
        (2, minute(1), None),  # missing reading: breaks the run
        (2, minute(2), 36.0),
        (3, minute(0), 31.0),
        (3, minute(1), float("nan")),  # glitch
        (3, minute(2), 32.0),
    )
    readings_table = catalog.create_table("plant.readings", schema=READING)
    readings_table.append(first)
    return (
        ENGINES,
        IcebergSink,
        IcebergSource,
        PreconditionError,
        READING,
        UnsupportedError,
        catalog,
        first,
        ibis,
        minute,
        readings_batch,
        readings_table,
        sv,
        to_sql,
    )


@app.cell(hide_code=True)
def _(display, first):
    display.arrow(first, title="plant.readings (Iceberg)")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 2. The rule, and the first thing the checker says

    Straight from the catalogue, three high readings in a row:
    """)
    return


@app.cell
def _(ibis):
    def three_high(readings):
        w = ibis.window(group_by="device_id", order_by="ts")
        r = readings.mutate(
            p1=readings.temperature.lag(1).over(w), p2=readings.temperature.lag(2).over(w)
        )
        return r.filter((r.temperature > 30) & (r.p1 > 30) & (r.p2 > 30)).select(
            "device_id", "ts", "temperature"
        )

    return (three_high,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Whoever gets paged at 3 a.m. assumes that every alert means the
    temperature is above 30 and that one hot minute pages them once. We'll
    write both down and ask the checker, first with no assumptions about the
    input:
    """)
    return


@app.cell
def _(READING, ibis, sv, three_high):
    from ibis import _

    readings_schema = ibis.table(ibis.Schema.from_pyarrow(READING), name="readings")
    unkeyed = sv.verify(
        three_high(readings_schema), ensures=[_.temperature > 30, sv.unique("device_id", "ts")]
    )
    assert not unkeyed.deterministic
    assert [c.label for c in unkeyed.unproved] == ["unique(device_id, ts)"]
    return readings_schema, unkeyed


@app.cell(hide_code=True)
def _(mo, unkeyed):
    mo.md(unkeyed._repr_markdown_())
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    `temperature > 30` is proved: it holds whichever reading the engine takes
    as the previous one. One alert per device and minute is not, and the
    report warns that the result is not deterministic. If a device can send
    two readings with the same `ts`, which one is "previous" depends on how
    the engine breaks the tie, and a rerun may page you twice. The catalogue
    found this in 44 of its 139 queries (dedup, top-N, `LAG` over equal
    timestamps; see its [findings](../catalogue/FINDINGS.md)), and it is the
    most common way for engines to disagree.

    The fix is to state what the source promises: at most one reading per
    device and minute. The sensor team can make that promise, and the job
    checks it on every batch.

    ## 3. The NaN glitch

    With that key we try again, and also ask that no alert is a NaN, since
    the person paged needs a temperature:
    """)
    return


@app.cell
def _(readings_schema, sv, three_high):
    from ibis import _

    REQUIRES = {"readings": [sv.unique("device_id", "ts")]}
    ENSURES = [_.temperature > 30, ~_.temperature.isnan(), sv.unique("device_id", "ts")]
    keyed = sv.verify(three_high(readings_schema), requires=REQUIRES, ensures=ENSURES)
    assert keyed.deterministic and [c.label for c in keyed.unproved] == ["~_.temperature.isnan()"]
    return ENSURES, REQUIRES, keyed


@app.cell(hide_code=True)
def _(keyed, mo):
    mo.md(keyed._repr_markdown_())
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    `temperature > 30` and the key are proved now. The checker refuses
    `~isnan()` rightly: in SQL `NaN > 30` is TRUE, since NaN sorts above
    every number, so device 3's glitch counts as hot and pages someone.
    Python says the opposite, which is how a rule tested in pandas
    misbehaves in the warehouse:
    """)
    return


@app.cell
def _():
    import duckdb

    {
        "Python: nan > 30": float("nan") > 30,  # noqa: PLW0177
        "DuckDB: 'nan'::double > 30": duckdb.sql("select 'nan'::double > 30").fetchall()[0][0],
    }
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    So we define a high reading to exclude NaN. NaN then breaks the run, as
    a missing reading does:
    """)
    return


@app.cell
def _(ENSURES, REQUIRES, ibis, sv):
    @sv.transform(requires=REQUIRES, ensures=ENSURES)
    def alerts(readings):
        w = ibis.window(group_by="device_id", order_by="ts")
        r = readings.mutate(
            p1=readings.temperature.lag(1).over(w), p2=readings.temperature.lag(2).over(w)
        )

        def high(c):
            return (c > 30) & ~c.isnan()

        return r.filter(high(r.temperature) & high(r.p1) & high(r.p2)).select(
            "device_id", "ts", "temperature"
        )

    return (alerts,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 4. Both rules on the data

    We put both versions side by side as nodes over the Iceberg source and
    refresh them together with `sv.group`, so they see the same snapshot.
    The naive rule is a plain function with no contract. Building the
    `alerts` node proves its contract:
    """)
    return


@app.cell
def _(IcebergSource, alerts, catalog, sv, three_high):
    readings = IcebergSource(catalog, "plant.readings")
    naive = readings.pipe(three_high)  # a plain function: no contract
    alerts_node = readings.pipe(alerts)
    report = alerts.report
    assert report.proved and report.deterministic
    sv.group(naive, alerts_node).refresh()
    assert sorted(naive.to_arrow()["device_id"].to_pylist()) == [1, 3]
    assert alerts_node.to_arrow()["device_id"].to_pylist() == [1]
    return alerts_node, naive, readings, report


@app.cell(hide_code=True)
def _(alerts_node, display, mo, naive, report):
    mo.vstack(
        [
            mo.md(report._repr_markdown_()),
            display.side_by_side(
                display.arrow(naive.to_arrow().sort_by("device_id"), title="naive rule"),
                display.arrow(alerts_node.to_arrow(), title="alerts (contracted)"),
            ),
            mo.md(
                "The naive rule alerts on device 3 because of the NaN; the contracted one doesn't. "
                "Device 2's missing reading breaks its run in both."
            ),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 5. Every engine, and the warehouses

    The alerts may run on a laptop today and in a warehouse tomorrow.
    DuckDB and Polars run the checked plan with the same rows, whichever
    `engine=` the node is refreshed with ([the engines](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/stability.md#engines)). Snowflake
    and Spark tables have no row order, so sverify refuses to write a window
    for them unless you promise that the order keys have no ties. The
    report's `deterministic` is that promise, proved from the key, so it can
    be passed on:
    """)
    return


@app.cell
def _(ENGINES, UnsupportedError, alerts, alerts_node, readings, report, to_sql):
    _rows = {}
    for _engine in ENGINES:
        _node = readings.pipe(alerts)
        _node.refresh(engine=_engine)
        _rows[_engine] = sorted(map(repr, _node.to_arrow().to_pylist()))
    assert len({repr(r) for r in _rows.values()}) == 1

    try:
        to_sql(alerts_node.internal_plan, "snowflake")
    except UnsupportedError as e:
        refused = str(e)
    _sql = to_sql(alerts_node.internal_plan, "snowflake", deterministic=report.deterministic)
    assert _sql.startswith("SELECT")
    refused
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    With `deterministic=True` the SQL is written. Without the key, `deterministic`
    would be `False`, and passing `deterministic=True` anyway would be an
    unproved promise.

    ## 6. New readings, and a sensor that sends twice

    Windows that share one `PARTITION BY` recompute only the partitions a
    batch touches, for inputs without ties on the partition and sort columns
    ([the guide](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/guide.md#nodes-composing-storing-refreshing)). The
    node's status says how it is refreshed, and its change flows to the
    sink and to nodes downstream:
    """)
    return


@app.cell
def _(alerts_node):
    print(alerts_node.status())
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    We store the node in an Iceberg sink with `.write`, and its first
    refresh writes the first state. The sink keeps the contract in the table
    properties and in every snapshot summary:
    """)
    return


@app.cell
def _(IcebergSink, alerts_node, catalog):
    stored = alerts_node.write(IcebergSink(catalog, "plant.alerts"))
    print(stored.refresh())
    return (stored,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Device 2 keeps running hot, and two more readings arrive. Iceberg
    appends are read from the files they added, and the keys of the new
    rows are checked against the rows kept:
    """)
    return


@app.cell
def _(alerts, minute, readings, readings_batch, readings_table, stored):
    readings_table.append(readings_batch((2, minute(3), 37.0), (2, minute(4), 38.0)))
    print(stored.refresh())
    _from_scratch = readings.pipe(alerts)
    _from_scratch.refresh()
    _rows = sorted(map(repr, stored.to_arrow().to_pylist()))
    assert _rows == sorted(map(repr, _from_scratch.to_arrow().to_pylist()))
    assert sorted(stored.to_arrow()["device_id"].to_pylist()) == [1, 2]
    return


@app.cell(hide_code=True)
def _(display, stored):
    display.arrow(stored.to_arrow().sort_by("device_id"), title="alerts")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Device 2's 12:03 reading doesn't alert because 12:01 was missing; 12:04
    does.

    Then device 1 sends two readings for 12:04. The key rules out exactly
    this case, which would make the alerts depend on the engine. The refresh
    refuses the batch and changes nothing: the node and the sink stay at the
    last good version, and the next refresh retries from there.
    """)
    return


@app.cell
def _(PreconditionError, minute, readings_batch, readings_table, stored):
    readings_table.append(readings_batch((1, minute(4), 34.0), (1, minute(4), 34.5)))
    try:
        stored.refresh()
    except PreconditionError as e:
        rejected = str(e)
    assert stored.versions == {"readings": 2}
    rejected
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## What you got

    You now have alerts the on-call engineer can rely on. The checker found
    two bugs before anything ran, an alert that depended on how ties were
    broken and a NaN reading that would have paged someone. The key is
    checked on every batch, so a sensor that sends twice stops the job and
    leaves the alerts as they were. The same plan runs on DuckDB and Polars,
    and Snowflake or Spark SQL is written once the tie-freedom
    it needs is proved. The window node says how it stays up to date, and
    its change is written to the sink.

    Next up: [An orders mart in SQL and Ibis](?file=03_orders_mart.py),
    where a dashboard's dbt tests become a contract.
    [Contracts](?file=04_contracts.py) covers windows, ties and the other
    double semantics in depth.
    """)
    return


if __name__ == "__main__":
    app.run()

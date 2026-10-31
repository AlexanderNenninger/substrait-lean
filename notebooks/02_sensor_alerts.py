# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "duckdb",
#     "ibis-framework==12.0.0",
#     "marimo",
#     "pyiceberg[sql-sqlite]",
#     "sverify[datafusion,polars,iceberg]",
# ]
#
# [tool.uv.sources]
# sverify = { path = "../python", editable = true }
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="medium", app_title="2. Sensor alerts")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 1. [Duplicate card payments](?file=01_duplicate_payments.py) · [Contents](?file=00_start_here.py) · 3. [An orders mart](?file=03_orders_mart.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 2. Sensor alerts from an Iceberg table

    Say you look after a plant whose temperature sensors write a reading
    per device per minute to an Iceberg table. Operations wants an **alert
    at every reading that is the third or more in a row above 30 °C**
    (`iot-consecutive-threshold` in the
    [query catalogue](../catalogue/INDEX.md), Azure Stream Analytics'
    `MATCH_RECOGNIZE` example), and someone on call will be woken up by
    each one. In SQL that is two `LAG`s over a window.

    Window queries are where engines quietly disagree. Three things go
    wrong in practice, and we'll run into each:

    * **ties**: two readings of a device at the same instant make
      "previous reading" ambiguous, and each engine picks one;
    * **NaN**: a glitching sensor sends NaN, and in SQL `NaN > 30` is TRUE
      (NaN sorts above every number), while in Python and pandas it is
      False, so a prototype and the production job disagree;
    * **warehouses without row order**: Snowflake and Spark tables have no
      order to break ties with.

    As in chapter 1, the job reads the source, states and proves a contract,
    runs on every engine, keeps up with new data and writes a sink.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 1. The source: an Iceberg table of readings

    Iceberg wants a catalog, so a small SQLite one in a temporary folder
    plays the part of Glue, a REST catalog or Unity. `device_id` and `ts`
    are `required`. Two of the devices are troublemakers: device 2 skipped
    a reading (NULL), and device 3 had a glitch and sent NaN. We'll see what
    each of them does to the alerts.
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
        IcebergSink,
        IcebergSource,
        READING,
        catalog,
        first,
        ibis,
        minute,
        readings_batch,
        readings_table,
        sv,
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
    Think of whoever gets paged at 3 a.m. They'll assume that every alert
    means the temperature really is above 30, and that one hot minute pages
    them once, not three times. Those are reasonable things to rely on, so
    let's write them down and ask the checker. First, with no assumptions
    about the input:
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
    return readings_schema, unkeyed


@app.cell(hide_code=True)
def _(mo, unkeyed):
    mo.md(unkeyed._repr_markdown_())
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Nothing is proved, not even `temperature > 30`, which is in the filter.
    The verdict is **undetermined**: if a device can send two readings with
    the same `ts`, which one is "previous" depends on how the engine breaks
    the tie, and engines break ties differently from run to run. The
    catalogue found this in 44 of its 139 queries (dedup, top-N, `LAG` over
    equal timestamps); it is the most common way for engines to disagree.

    The fix is to say what the source promises: at most one reading per
    device and minute. That's a promise the sensor team can make, and one
    we'll hold them to later.

    ## 3. The NaN glitch

    With that key, let's try again, and also ask that no alert is a NaN:
    the person paged would like a temperature, not a glitch.
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
    `temperature > 30` and the key are proved now. `~isnan()` is refused,
    and the checker is right: in SQL a NaN is greater than every number, so
    device 3's glitch counts as a high reading and the alert fires. Python
    says the opposite, which is how a rule tested in pandas misbehaves in
    the warehouse:
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
    So let's say what a high reading is. NaN then breaks the run, like a
    missing reading does:
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
    ## 4. The pipeline

    Let's put both versions side by side as views over the Iceberg source,
    and compare them on the data. Building the `alerts` view proves its
    contract:
    """)
    return


@app.cell
def _(IcebergSource, alerts, catalog, sv, three_high):
    pipe = sv.Pipeline(sv.connect())
    readings = pipe.source("readings", IcebergSource(catalog, "plant.readings"))
    naive = pipe.view("naive_alerts", three_high(readings))
    view = pipe.view("alerts", alerts(readings))
    report = alerts.last_report
    assert report.proved and report.deterministic
    assert [r[0] for r in naive.rows()] == [1, 3] and [r[0] for r in view.rows()] == [1]
    return naive, pipe, report, view


@app.cell(hide_code=True)
def _(display, mo, naive, report, view):
    mo.vstack(
        [
            mo.md(report._repr_markdown_()),
            display.side_by_side(
                display.table(naive.rows(), naive.columns, title="naive rule"),
                display.table(view.rows(), view.columns, title="alerts (contracted)"),
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

    The alerts may run on a laptop today and in the warehouse tomorrow.
    DuckDB, Polars and DataFusion run the checked plan with the same rows.
    Snowflake and Spark tables have no row order, so sverify **refuses** to
    write a window for them unless you promise the order keys have no ties.
    The report's `deterministic` is exactly that promise, proved from the
    key, so it can be passed on:
    """)
    return


@app.cell
def _(pipe, report, sv, view):
    import json

    from sverify.sql import Unsupported, to_sql
    from sverify.sql.snowflake import SNOWFLAKE

    _rows = {e: sv.run_plan(pipe.con, view.plan, e).to_pylist() for e in sv.ENGINES}
    assert len({repr(r) for r in _rows.values()}) == 1

    try:
        to_sql(json.loads(view.plan), SNOWFLAKE)
    except Unsupported as e:
        refused = str(e)
    _sql = to_sql(json.loads(view.plan), SNOWFLAKE, tie_free=report.deterministic)
    assert _sql.startswith("SELECT")
    refused
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    With `tie_free=True` the SQL is written. Without the key, `deterministic`
    would be `False`, and passing `tie_free=True` anyway would be an
    unproved promise.

    ## 6. New readings, and a sensor that sends twice

    A window isn't incrementally maintainable (yet), and the pipeline says
    so up front instead of maintaining it incorrectly. Such a view is
    **recomputed and diffed** on each refresh; its change still flows to the
    sink and to views downstream:
    """)
    return


@app.cell
def _(pipe):
    pipe.fallbacks
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The first state goes to an Iceberg sink, which keeps the contract in the
    table properties and in every snapshot summary:
    """)
    return


@app.cell
def _(IcebergSink, catalog, view):
    sink = IcebergSink(catalog, "plant.alerts", view)
    print(sink.write())
    return (sink,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Device 2 keeps running hot, and two more readings arrive. Iceberg
    appends are read from the files they added, and the keys of the new
    rows are checked against the rows kept:
    """)
    return


@app.cell
def _(minute, pipe, readings_batch, readings_table, sink, view):
    readings_table.append(readings_batch((2, minute(3), 37.0), (2, minute(4), 38.0)))
    print(pipe.refresh())
    print(sink.write())
    assert view.rows() == view.recompute() and [r[0] for r in view.rows()] == [1, 2]
    return


@app.cell(hide_code=True)
def _(display, view):
    display.table(view.rows(), view.columns, title="alerts")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Device 2's 12:03 reading doesn't alert (12:01 was missing); 12:04 does.

    Then device 1 gets enthusiastic and sends two readings for 12:04. That
    is exactly the case the key rules out, and the one that would make the
    alerts depend on the engine. The refresh refuses the batch, and
    **nothing changes**: the view and the sink stay at the last good
    version, and the next refresh retries from there.
    """)
    return


@app.cell
def _(minute, pipe, readings_batch, readings_table, sv, view):
    readings_table.append(readings_batch((1, minute(4), 34.0), (1, minute(4), 34.5)))
    try:
        pipe.refresh()
    except sv.PreconditionError as e:
        rejected = str(e)
    assert view.versions == {"readings": 2}
    rejected
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## What you got

    * The checker found **two real bugs before anything ran**: the rule's
      result depended on tie-breaking without a key, and a NaN reading
      raised a false alert. Nobody was paged for either.
    * The key is checked on every batch, so a sensor sending twice stops the
      job instead of making it engine-dependent.
    * The same plan runs on DuckDB, Polars and DataFusion, and sverify
      writes Snowflake or Spark SQL only when the tie-freedom it needs is
      proved.
    * The window view is honest about not being incremental, and is kept
      up to date by recomputation, with its change written to the sink.

    **Next:** [An orders mart in SQL and Ibis](?file=03_orders_mart.py).
    Windows and ties are covered in depth in
    [Windows and ASOF joins](?file=07_windows_and_asof.py), NaN and other
    double semantics in [Doubles, time and text](?file=12_values.py).
    """)
    return


if __name__ == "__main__":
    app.run()

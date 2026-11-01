# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "ibis-framework==12.0.0",
#     "marimo",
#     "sverify[datafusion]==0.3.0",
# ]
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="medium", app_title="7. Windows and ASOF joins")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 6. [Runtime errors](?file=06_runtime_errors.py) · [Contents](?file=00_start_here.py) · 8. [Composing contracts](?file=08_composition.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 7. Windows and ASOF joins

    Say the maintenance team asks how long each sensor went quiet between
    readings, because a long silence means a unit they should replace
    before it fails outright. For that you need, for every reading, the one
    before it.

    Time-series pipelines constantly look at *neighbouring* rows like this:
    the previous reading of the same sensor, the next event of the same
    user, the position of a row within its group. SQL does this with
    **window functions**:

    ```sql
    LAG(ts) OVER (PARTITION BY sensor ORDER BY ts)
    ```

    reads "for each row, the `ts` of the previous row of the same sensor,
    in `ts` order" (NULL for the first one). The model supports `LAG`,
    `LEAD` and `ROW_NUMBER`, with any sort directions, NULLs first or last,
    offsets and defaults (`SubstraitLean/Window.lean`).

    ## LAG, LEAD and ROW_NUMBER
    """)
    return


@app.cell
def _():
    import datetime as dt

    import ibis
    import sverify as sv
    from sverify.engines import create_table

    def t(m, s=0):
        return dt.datetime(2024, 5, 1, 7, m, s)

    con = sv.connect()
    create_table(
        con,
        "readings",
        ibis.schema({"sensor": "string", "ts": "timestamp", "v": "float64"}),
        [("a", t(0), 1.0), ("a", t(5), 1.5), ("a", t(7), 1.2), ("b", t(1), 9.0), ("b", t(4), 8.5)],
    )

    def with_neighbours(readings):
        w = ibis.window(group_by=readings.sensor, order_by=readings.ts)
        return readings.select(
            "sensor",
            "ts",
            "v",
            prev_ts=readings.ts.lag().over(w),
            next_v=readings.v.lead().over(w),
            rn=ibis.row_number().over(w),
        )

    return con, create_table, dt, ibis, sv, t, with_neighbours


@app.cell(hide_code=True)
def _(con, display, with_neighbours):
    display.arrow(
        with_neighbours(con.table("readings")).order_by("sensor", "ts"),
        title="with_neighbours(readings)",
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    (Ibis numbers rows from 0.) What can be proved about these columns?
    Lean knows that `LAG(ts)` comes from an **earlier** row of the same
    partition, so `prev_ts <= ts`; that a lagged partition column equals the
    row's own; and that `ROW_NUMBER()` is never negative. Guard the first
    row's NULL with `isnull() | …`, as in the contract below.

    ## Ties: when "previous" isn't well defined

    Sensors sometimes report twice in the same instant. If two readings of
    a sensor have the **same** `ts`, which one is "previous"? SQL doesn't
    say; the engine picks, and may pick differently on the next run. A
    proof about one choice would say nothing about the other. So unless
    `requires` gives a key on the partition and order columns, Lean
    reports every postcondition as *undetermined* and
    `report.deterministic` is `False`. With the key, earlier means strictly
    earlier: `prev_ts < ts`.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    keyed = mo.ui.switch(value=True, label="requires unique(sensor, ts)")
    keyed
    return (keyed,)


@app.cell
def _(ibis, keyed, mo, sv, with_neighbours):
    from ibis import _

    readings = ibis.table({"sensor": "string", "ts": "timestamp", "v": "float64"}, name="readings")
    _requires = [_.sensor.notnull(), _.ts.notnull()] + (
        [sv.unique("sensor", "ts")] if keyed.value else []
    )
    _report = sv.verify(
        with_neighbours(readings),
        requires={"readings": _requires},
        ensures=[_.prev_ts.isnull() | (_.prev_ts < _.ts), _.rn >= 0],
    )
    mo.vstack([mo.md(f"`report.deterministic` is **{_report.deterministic}**"), _report])
    return (readings,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The theorem that makes the keyed case trustworthy is `window_tiebreak`
    (`SubstraitLean/Keys.lean`): when a window's partition and sort columns
    contain a key of its input, **every** way of sorting the input by the
    window's keys gives the same rows. So the proof describes what
    DataFusion computes, however it breaks ties internally.

    ## ASOF joins: aligning two sensors

    An accelerometer samples at 100 Hz, a gyroscope at 130 Hz, so their
    timestamps rarely line up. To train a model on both you want, for each
    accelerometer sample, the **latest gyroscope sample at or before it**,
    and only if it is recent enough. That is an *ASOF join*. DataFusion
    doesn't have one (and Ibis's `asof_join` compiles to DuckDB syntax), so
    `sv.asof_join` builds it from parts Lean understands: a range join, then
    `ROW_NUMBER` to keep the latest match.

    The model will be trained on these pairs, so a gyroscope reading from
    the future would quietly leak information it can't have in production.
    The contract says what an ASOF join promises: one output row per
    accelerometer sample, never a gyroscope sample from the future, and
    never one older than the tolerance.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    tolerance_ms = mo.ui.slider(1, 20, value=10, label="tolerance (ms)", show_value=True)
    how = mo.ui.radio(["left", "inner"], value="left", label="how", inline=True)
    gyr_keyed = mo.ui.switch(value=True, label="requires gyr: unique(device, ts)")
    mo.hstack([tolerance_ms, how, gyr_keyed], justify="start", gap=2)
    return gyr_keyed, how, tolerance_ms


@app.cell
def _(con, create_table, dt, gyr_keyed, how, ibis, sv, tolerance_ms):
    from ibis import _

    _t0 = dt.datetime(2024, 5, 1, 7, 0)
    _acc = [(1, _t0 + dt.timedelta(microseconds=10_000 * i), float(i)) for i in range(100)]
    _gyr = [
        (1, _t0 + dt.timedelta(microseconds=round(1e6 * i / 130)), float(i)) for i in range(130)
    ]
    create_table(
        con, "acc", ibis.schema({"device": "int64", "ts": "timestamp", "a": "float64"}), _acc
    )
    create_table(
        con, "gyr", ibis.schema({"device": "int64", "ts": "timestamp", "g": "float64"}), _gyr
    )

    tol = ibis.interval(milliseconds=tolerance_ms.value)

    @sv.transform(
        requires={
            "acc": [sv.unique("device", "ts"), _.device.notnull(), _.ts.notnull()],
            "gyr": [sv.unique("device", "ts")] if gyr_keyed.value else [],
        },
        ensures=[
            sv.unique("device", "ts"),  # one row per accelerometer sample
            _.ts_right.isnull() | (_.ts_right <= _.ts),  # never from the future
            # never too old (a condition can be SQL, too)
            f"ts_right IS NULL OR ts_right >= ts - INTERVAL '{tolerance_ms.value} milliseconds'",
        ],
        on_unproved="warn",
    )
    def aligned(acc, gyr):
        return sv.asof_join(acc, gyr, on="ts", by="device", tolerance=tol, how=how.value)

    aligned_rows = aligned(con.table("acc"), con.table("gyr")).order_by("ts").to_pyarrow()
    aligned.last_report
    return (aligned_rows,)


@app.cell(hide_code=True)
def _(aligned_rows, display, mo):
    _rows = aligned_rows.to_pylist()
    _matched = sum(r["ts_right"] is not None for r in _rows)
    mo.vstack(
        [
            mo.md(
                f"**{len(_rows)}** output rows for 100 accelerometer samples; "
                f"**{_matched}** found a gyroscope sample within the tolerance."
            ),
            display.arrow(aligned_rows.slice(0, 8), title="the first rows"),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Things to try:

    * **Lower the tolerance** below 8 ms. The gyroscope samples every 7.7 ms,
      so some accelerometer samples find no partner. With `how="left"` they
      stay, with NULLs; with `"inner"` they disappear. The proofs hold
      either way.
    * **Drop the key on `gyr`.** Two gyroscope readings at the same instant
      would tie for "latest", so the result is undetermined, and every
      postcondition is refused (here as a warning, thanks to
      `on_unproved="warn"`).

    One-row-per-sample comes from the key analysis: `ROW_NUMBER()` over a
    partition is a key together with the partition columns, and the filter
    `rank = 0` drops the rank from that key.

    Windows are covered by contracts but **not maintained incrementally**
    yet: chapter 10 shows how a pipeline recomputes such views instead.
    Framed aggregates (`AVG(v) OVER (ROWS 5 PRECEDING)`), `RANK` and running
    sums are not supported yet.

    You can now prove facts about neighbouring rows, tell when ties leave a
    window's result up to the engine, and align two sensors with an ASOF
    join that never reaches into the future. The maintenance team's gaps
    and the model's training pairs both rest on proofs. **Next up:**
    [Composing contracts](?file=08_composition.py), where one step's
    promises become the next step's assumptions.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 6. [Runtime errors](?file=06_runtime_errors.py) · [Contents](?file=00_start_here.py) · 8. [Composing contracts](?file=08_composition.py) →
    """)
    return


if __name__ == "__main__":
    app.run()

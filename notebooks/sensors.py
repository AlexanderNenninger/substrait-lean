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
app = marimo.App(width="medium", app_title="Aligning sensors, provably")


@app.cell(hide_code=True)
def _():
    import marimo as mo

    return (mo,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # Aligning sensors, provably

    A phone records motion with two sensors that don't tick together: the
    accelerometer samples at **100 Hz** (every 10 ms), the gyroscope at
    **130 Hz** (every ~7.7 ms). To train a model you need one row per
    accelerometer sample with *the latest gyroscope reading at or before it*.
    That is an **ASOF join**, and it is easy to get subtly wrong: a match from
    the future leaks information, a stale match is noise, a duplicate row
    double-counts.

    This notebook states those three properties as a contract, has Lean prove
    them for every possible input, and then shows the one situation (ties)
    where Lean refuses to claim anything, and why it is right to. Along the way
    it uses `LAG` to find the gaps where the gyroscope dropped out.

    New to the ideas here? Start with `notebooks/intro.py`.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 1. The data

    Two devices, 200 ms each. Device 2's gyroscope drops out between roughly
    60 ms and 115 ms.
    """)
    return


@app.cell
def _():
    import datetime as dt

    import ibis

    import sverify as sv
    from sverify.engine import run_sql, to_sql

    T0 = dt.datetime(2024, 5, 1, 7, 0)

    def at(ms):
        """The timestamp `ms` milliseconds after T0."""
        return T0 + dt.timedelta(microseconds=round(1000 * ms))

    def schema(value):
        return ibis.schema({"device": "int64", "ts": "timestamp", value: "float64"})

    acc_rows = [(d, at(10 * i), round(0.1 * i, 1)) for d in (1, 2) for i in range(20)]
    gyr_rows = [
        (d, at(1000 * i / 130), float(i))
        for d in (1, 2)
        for i in range(26)
        if not (d == 2 and 8 <= i <= 14)  # the dropout
    ]

    con = sv.connect()  # an Ibis DataFusion backend
    sv.create_table(con, "acc", schema("ax"), acc_rows)
    sv.create_table(con, "gyr", schema("gx"), gyr_rows)
    acc, gyr = con.table("acc"), con.table("gyr")
    return T0, acc, at, con, gyr, gyr_rows, ibis, run_sql, schema, sv, to_sql


@app.cell(hide_code=True)
def _(T0, con, run_sql, to_sql):
    def rows(expr):
        """Run an Ibis expression on DataFusion, with times as milliseconds
        after 07:00. (Ibis's own `to_pyarrow` rounds durations to seconds.)"""
        out = []
        for r in run_sql(con, to_sql(expr)).to_pylist():
            for k, v in r.items():
                if hasattr(v, "hour"):
                    r[k] = round((v - T0).total_seconds() * 1000, 1)
            out.append(r)
        return out

    return (rows,)


@app.cell(hide_code=True)
def _(acc, gyr, mo, rows):
    mo.hstack(
        [
            mo.vstack([mo.md("**acc** (ts in ms)"), mo.ui.table(rows(acc), selection=None, page_size=6)]),
            mo.vstack([mo.md("**gyr** (ts in ms)"), mo.ui.table(rows(gyr), selection=None, page_size=6)]),
        ],
        justify="start",
        gap=2,
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 2. The ASOF join and its contract

    DataFusion has no ASOF join, so `sv.asof_join` builds one from parts Lean
    understands: a range join (same device, gyroscope at or before the
    accelerometer, at most `tolerance` earlier), then `ROW_NUMBER()` per
    accelerometer sample, latest match first, keeping number 0.

    The contract says what an ASOF join promises:

    * `unique(device, ts)`: **one row per accelerometer sample**, never two;
    * `ts_right <= ts`: the gyroscope reading is **never from the future**;
    * `ts_right >= ts - 10 ms`: it is **never stale**.

    `ts_right` is the matched gyroscope time, NULL when nothing is close enough.
    """)
    return


@app.cell
def _(ibis, sv):
    from ibis import _

    TOLERANCE = ibis.interval(milliseconds=10)
    KEYS = {
        "acc": [sv.unique("device", "ts"), _.device.notnull(), _.ts.notnull()],
        "gyr": [sv.unique("device", "ts")],
    }

    @sv.transform(
        requires=KEYS,
        ensures=[
            sv.unique("device", "ts"),
            "ts_right IS NULL OR ts_right <= ts",
            "ts_right IS NULL OR ts_right >= ts - INTERVAL '10 milliseconds'",
        ],
    )
    def aligned(acc, gyr):
        return sv.asof_join(acc, gyr, on="ts", by="device", tolerance=TOLERANCE)

    return KEYS, aligned


@app.cell
def _(acc, aligned, gyr, mo):
    matched = aligned(acc, gyr)  # checks `requires` on the data, proves `ensures`
    mo.md(aligned.last_report._repr_markdown_())
    return (matched,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    All three are **proved**: not on these 40 rows, but for every pair of
    tables satisfying `requires`. Lean works it out from the plan alone:

    * The join condition `gyr.ts <= acc.ts` becomes a fact about every joined
      row, and so does `gyr.ts >= acc.ts - 10 ms`. Both survive the `ROW_NUMBER`
      and the filter, so they hold on the output.
    * The row number, numbered per `(device, ts)`, makes `(device, ts, row
      number)` a key. Keeping only row number 0 fixes that column, which
      leaves `(device, ts)` as the key.
    * `requires` is checked on the data when you call `aligned` on real
      tables: if the inputs broke it, you'd get a `PreconditionError` instead
      of a result (section 4 shows one).

    Here is what the join matched. Each accelerometer sample (top row of ticks
    per device) is linked to its gyroscope reading (bottom row); red samples
    found none within the tolerance:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    def timeline(matches, gyr_times, width=680):
        """Ticks for both sensors per device, with a line per match."""
        span, left, row_h = 200.0, 40, 70

        def x(ms):
            return left + (width - left - 10) * ms / span

        parts = []
        for i, device in enumerate((1, 2)):
            top, bottom = 20 + i * row_h, 20 + i * row_h + 34
            parts.append(
                f"<text x='0' y='{top + 20}' font-size='11' fill='currentColor'>dev {device}</text>"
            )
            for t in gyr_times[device]:
                parts.append(
                    f"<line x1='{x(t):.1f}' y1='{bottom}' x2='{x(t):.1f}' y2='{bottom + 8}'"
                    " stroke='#3b82c4' stroke-width='2'/>"
                )
            for m in (m for m in matches if m["device"] == device):
                ok = m["ts_right"] is not None
                color = "currentColor" if ok else "#d64545"
                parts.append(
                    f"<line x1='{x(m['ts']):.1f}' y1='{top - 8}' x2='{x(m['ts']):.1f}' y2='{top}'"
                    f" stroke='{color}' stroke-width='2'/>"
                )
                if ok:
                    parts.append(
                        f"<line x1='{x(m['ts']):.1f}' y1='{top}' x2='{x(m['ts_right']):.1f}' y2='{bottom}'"
                        " stroke='currentColor' stroke-opacity='.35'/>"
                    )
        legend = (
            f"<text x='{left}' y='{20 + 2 * row_h}' font-size='11' fill='currentColor'>"
            "top ticks: accelerometer · <tspan fill='#3b82c4'>bottom ticks: gyroscope</tspan>"
            " · <tspan fill='#d64545'>red: no match</tspan> · 0 to 200 ms</text>"
        )
        return mo.Html(
            f"<svg viewBox='0 0 {width} {28 + 2 * row_h}' width='100%' style='max-width:{width}px'>"
            + "".join(parts)
            + legend
            + "</svg>"
        )

    return (timeline,)


@app.cell(hide_code=True)
def _(gyr, matched, rows, timeline):
    gyr_times = {d: [r["ts"] for r in rows(gyr) if r["device"] == d] for d in (1, 2)}
    timeline(rows(matched), gyr_times)
    return (gyr_times,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 3. Change the tolerance, change the proof

    The contract is re-proved for whatever you pick below. Lean proves the
    staleness bound that the join actually enforces, and refuses a tighter
    one. Turn off the gyroscope key and see what happens to *all* of it.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    tolerance_ms = mo.ui.slider(2, 30, value=10, label="join tolerance (ms)", show_value=True)
    claimed_ms = mo.ui.slider(2, 30, value=10, label="ensures: never older than (ms)", show_value=True)
    gyr_keyed = mo.ui.switch(value=True, label="requires unique(device, ts) on gyr")
    mo.vstack([tolerance_ms, claimed_ms, gyr_keyed])
    return claimed_ms, gyr_keyed, tolerance_ms


@app.cell(hide_code=True)
def _(
    KEYS,
    acc,
    claimed_ms,
    gyr,
    gyr_keyed,
    gyr_times,
    ibis,
    mo,
    rows,
    sv,
    timeline,
    tolerance_ms,
):
    _joined = sv.asof_join(
        acc, gyr, on="ts", by="device", tolerance=ibis.interval(milliseconds=tolerance_ms.value)
    )
    _report = sv.verify(
        _joined,
        requires=KEYS if gyr_keyed.value else {"acc": KEYS["acc"]},
        ensures=[
            sv.unique("device", "ts"),
            "ts_right IS NULL OR ts_right <= ts",
            f"ts_right IS NULL OR ts_right >= ts - INTERVAL '{claimed_ms.value} milliseconds'",
        ],
    )
    _rows = rows(_joined)
    _unmatched = sum(r["ts_right"] is None for r in _rows)
    mo.vstack(
        [
            mo.md(_report._repr_markdown_()),
            timeline(_rows, gyr_times),
            mo.md(f"{len(_rows)} rows, {_unmatched} without a gyroscope reading."),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Things to notice:

    * With a claim looser than the tolerance (say tolerance 5, claim 10), the
      claim is proved: it follows from the stricter one. A claim tighter than
      the tolerance is refused, and rightly: the longer lines in the timeline
      are matches older than the claim.
    * Without the key on `gyr`, **every** postcondition becomes
      *undetermined*, even "never from the future", which looks obviously
      true. The next section explains why that is the honest answer.

    ## 4. Ties: when the engine gets to choose

    "The latest reading at or before `ts`" assumes there *is* one latest
    reading. If the gyroscope reports twice at the same instant, two rows tie
    for first place in `ROW_NUMBER`'s order, and the SQL standard lets the
    engine pick either. DataFusion's choice can depend on how the data was
    partitioned, so the same query on the same data may give different
    answers on different runs or machines.

    Lean's semantics of windows sorts stably, which is *one* valid choice. A
    proof about one choice says nothing about the one DataFusion makes. So
    when the order can tie, the checker claims nothing at all
    (`report.deterministic` is `False`). With a key on `(device, ts)`, theorem
    `window_tiebreak` shows that every way of breaking ties gives the same
    rows, and the proofs apply to whatever DataFusion does.

    Make it real: add a second gyroscope reading at an instant that already has one.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    add_tie = mo.ui.switch(value=False, label="add a duplicate gyroscope reading (device 1 at 23.1 ms, gx = 99)")
    add_tie
    return (add_tie,)


@app.cell(hide_code=True)
def _(acc, add_tie, aligned, at, con, gyr_rows, mo, rows, schema, sv):
    _tied = gyr_rows + ([(1, at(3000 / 130), 99.0)] if add_tie.value else [])
    sv.create_table(con, "gyr_tied", schema("gx"), _tied)
    _gyr_tied = con.table("gyr_tied")
    # Every gyroscope reading that qualifies for the sample at 30 ms.
    _candidates = [
        r for r in rows(_gyr_tied) if r["device"] == 1 and 20 <= r["ts"] <= 30
    ]
    try:
        aligned(acc, _gyr_tied)
        _verdict = mo.callout(mo.md("`requires` holds, and the contract is proved."), kind="success")
    except sv.PreconditionError as _e:
        _verdict = mo.callout(
            mo.md(
                f"**`PreconditionError`**: {_e}. The call is refused before anything runs: "
                "the proof assumed this key, and the data breaks it."
            ),
            kind="danger",
        )
    mo.vstack(
        [
            _verdict,
            mo.md("Gyroscope readings within 10 ms before device 1's sample at **30 ms**:"),
            mo.ui.table(_candidates, selection=None),
            mo.md(
                "Two rows share the latest time: which `gx` the sample gets is up to the engine."
                if add_tie.value
                else "One latest reading: the match is determined."
            ),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    This is the division of labour in `sverify`: assumptions about incoming
    data (`requires`) are **checked** on the data, because no proof can know
    what a sensor will send; conclusions about the output (`ensures`) are
    **proved**, because they follow from the assumptions and the plan.

    ## 5. Finding dropouts with `LAG`

    Where did the gyroscope stop reporting? `LAG(ts)` over each device's
    readings, ordered by time, gives the previous reading's time. A gap
    longer than a threshold is a dropout.

    Lean knows what `LAG` means: the value comes from an *earlier* row of the
    same partition. With a key on `(device, ts)`, earlier is strictly earlier,
    so `prev_ts < ts` is proved, and so is the gap bound the filter enforces.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    gap_ms = mo.ui.slider(8, 60, value=20, label="a dropout is a gap longer than (ms)", show_value=True)
    explicit_null = mo.ui.switch(value=True, label="filter also says prev_ts IS NOT NULL")
    mo.vstack([gap_ms, explicit_null])
    return explicit_null, gap_ms


@app.cell
def _(explicit_null, gap_ms, gyr, ibis, mo, rows, sv):
    def dropouts(gyr, gap):
        w = ibis.window(group_by=gyr.device, order_by=gyr.ts)
        with_prev = gyr.select("device", "ts", prev_ts=gyr.ts.lag().over(w))
        long_gap = with_prev.ts > with_prev.prev_ts + gap
        if explicit_null.value:
            long_gap = with_prev.prev_ts.notnull() & long_gap
        return with_prev.filter(long_gap)

    _expr = dropouts(gyr, ibis.interval(milliseconds=gap_ms.value))
    _report = sv.verify(
        _expr,
        requires={"gyr": [sv.unique("device", "ts"), "device IS NOT NULL", "ts IS NOT NULL"]},
        ensures=[
            "prev_ts < ts",
            f"ts - prev_ts > INTERVAL '{gap_ms.value} milliseconds'",
            sv.unique("device", "ts"),
        ],
    )
    mo.vstack(
        [
            mo.md(_report._repr_markdown_()),
            mo.md("**Dropouts found** (times in ms):"),
            mo.ui.table(rows(_expr), selection=None),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Turn off the explicit `prev_ts IS NOT NULL` and the first two claims drop
    to "TRUE or NULL". Logically the filter `ts > prev_ts + gap` already rules
    out NULL (a NULL comparison is not TRUE, so the row is dropped), but Lean's
    analysis currently learns NULL-freedom only from comparisons with a
    constant, not from comparisons between two columns. It is **sound but
    incomplete**: when it can't prove something, it says so, and spelling the
    condition out is enough.

    ## 6. What this does not do (yet)

    * **Incremental maintenance.** Windows aren't in the incrementally
      maintainable fragment, so `sv.IncrementalView` refuses the ASOF join
      rather than maintaining it wrongly:
    """)
    return


@app.cell
def _(con, matched, sv):
    try:
        sv.IncrementalView(con, matched, "aligned_view")
        _msg = "accepted"
    except sv.NotIncremental as _e:
        _msg = f"NotIncremental: {_e}"
    _msg
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    * **Completeness.** The contract says every output row is a correct
      match. The converse, "every sample with a reading within 10 ms *is*
      matched", is a separate Lean theorem per plan today
      (`IoT.window_complete` in `SubstraitLean/Completeness.lean`), not
      something the checker reports.
    * **Double arithmetic.** Comparisons on doubles are exact (NaN and −0.0
      included, with DataFusion's ordering), but `gx * 2.5` is only known to be
      "some double", because rounding isn't modelled.

    **Proved**: the window semantics, the key and tie-breaking analysis, the
    relations taken from join and filter conditions, and `contract_sound`,
    which ties it together. **Trusted**: the translation from DataFusion's
    Substrait plan into the Lean model, and DataFusion itself; randomized tests
    in `python/tests/test_asof.py` and `test_windows.py` run Lean's interpreter
    against DataFusion on generated tables to keep that boundary honest.
    """)
    return


if __name__ == "__main__":
    app.run()

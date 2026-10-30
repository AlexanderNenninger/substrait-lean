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
app = marimo.App(width="medium", app_title="A verified fitness pipeline")


@app.cell(hide_code=True)
def _():
    import marimo as mo

    return (mo,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # A verified fitness pipeline

    A watch streams heart-rate samples, and users log workouts in an app. For
    training a model we want **the heart rate during each workout**, with
    sensor glitches removed. The pipeline is a few lines of Ibis; the
    interesting part is the *contract* on it:

    * **requires**: what we assume about the inputs (at most one sample per
      user and timestamp; every workout has a start and an end);
    * **ensures**: what the output must satisfy (plausible heart rates, no
      NaN, every sample inside its workout, one row per user and timestamp).

    Lean checks every `ensures` against the pipeline's Substrait plan *before
    any data runs*. A ✅ is a proof for **all** possible inputs that satisfy
    `requires`, not a test on the rows below. Then the same pipeline runs as
    an incrementally maintained view whose update rules are proved correct
    too.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 1. The data

    Real sensor data is messy: `-1` means the sensor lost contact, and the
    occasional `NaN` slips through. User 2's 09:00 sample is outside any
    workout.
    """)
    return


@app.cell
def _():
    import datetime as dt
    import warnings

    import ibis

    import sverify as sv

    def t(h, m):
        return dt.datetime(2024, 5, 1, h, m)

    con = sv.connect()  # an Ibis DataFusion backend
    sv.create_table(
        con,
        "heart_rate",
        ibis.schema({"user_id": "int64", "ts": "timestamp", "bpm": "float64"}),
        [
            (1, t(7, 0), 72.0),
            (1, t(7, 5), 131.0),
            (1, t(7, 10), -1.0),  # lost contact
            (1, t(7, 15), 148.0),
            (2, t(7, 5), float("nan")),  # glitch
            (2, t(7, 10), 155.0),
            (2, t(9, 0), 64.0),  # not during a workout
        ],
    )
    sv.create_table(
        con,
        "workouts",
        ibis.schema({"user_id": "int64", "kind": "string", "start": "timestamp", "end": "timestamp"}),
        [(1, "run", t(7, 0), t(7, 30)), (2, "bike", t(7, 0), t(8, 0))],
    )
    hr, workouts = con.table("heart_rate"), con.table("workouts")
    return con, hr, sv, t, warnings, workouts


@app.cell(hide_code=True)
def _(hr, mo, workouts):
    mo.hstack(
        [
            mo.vstack([mo.md("**heart_rate**"), mo.ui.table(hr.to_pyarrow().to_pylist(), selection=None)]),
            mo.vstack([mo.md("**workouts**"), mo.ui.table(workouts.to_pyarrow().to_pylist(), selection=None)]),
        ],
        justify="start",
        gap=2,
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 2. The pipeline and its contract

    The decorator states the contract; the function body is ordinary Ibis.
    Conditions are Ibis expressions over the output columns (`_.bpm`), and
    `sv.unique(...)` says the listed columns form a key.

    `on_unproved="warn"` lets the call go through with a warning when Lean
    can't prove something; the default, `"error"`, refuses the pipeline, and
    `"runtime"` checks the unproved conditions on the actual output instead.
    """)
    return


@app.cell
def _(sv):
    from ibis import _

    @sv.transform(
        requires={
            "heart_rate": [sv.unique("user_id", "ts")],
            "workouts": [_.start.notnull(), _.end.notnull()],
        },
        ensures=[
            _.bpm >= 30,
            _.bpm <= 230,
            ~_.bpm.isnan(),
            _.ts >= _.start,
            _.ts < _.end,
            sv.unique("user_id", "ts"),
        ],
        on_unproved="warn",
    )
    def workout_heart_rate(heart_rate, workouts):
        valid = heart_rate.filter((heart_rate.bpm >= 30) & (heart_rate.bpm <= 230))
        return valid.join(
            workouts,
            (valid.user_id == workouts.user_id)
            & (valid.ts >= workouts.start)
            & (valid.ts < workouts.end),
        ).select(valid.user_id, workouts.kind, valid.ts, valid.bpm, workouts.start, workouts.end)

    return (workout_heart_rate,)


@app.cell
def _(hr, warnings, workout_heart_rate, workouts):
    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter("always")
        expr = workout_heart_rate(hr, workouts)
    report = workout_heart_rate.last_report
    return caught, expr, report


@app.cell(hide_code=True)
def _(caught, mo, report):
    mo.vstack(
        [
            mo.md(report._repr_markdown_()),
            mo.callout(mo.md(f"**Warning:** {caught[0].message}"), kind="warn") if caught else mo.md(""),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### Reading the verdicts

    * **`bpm >= 30`, `bpm <= 230`**: the filter keeps only those rows, and
      Lean tracks the interval of every column through the plan.
    * **`~bpm.isnan()`**: subtle! There is no NaN check in the pipeline. But
      DataFusion orders floats *totally*, with NaN above every number, so
      `NaN <= 230` is false and the filter already removes NaN. Lean models
      DataFusion's floats exactly, so it knows this. Careful: unlike in
      Python, `NaN >= 30` is TRUE in DataFusion, so a lower bound alone would
      let NaN through. Try it in section 3.
    * **`ts >= start`, `ts < end`**: the join condition holds for every
      joined row, and `requires` says `start` and `end` are never NULL, so
      the comparisons are TRUE rather than NULL.
    * **`unique(user_id, ts)`: refused, and rightly so.** Each sample is unique
      in `heart_rate`, but nothing stops a user from logging two *overlapping*
      workouts; a sample inside both would appear twice. Lean finds no proof
      because there is none. Section 4 makes the counterexample real.

    The **known values** table is everything Lean derived about the output,
    whether or not you asked: it is a free, proved data dictionary.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 3. Break the pipeline, watch the proof go

    Change the filter and the postconditions below are re-proved on the fly.
    Lower bounds under 30 lose `bpm >= 30`; drop the upper bound and NaN
    gets through, so `~bpm.isnan()` fails as well.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    lower = mo.ui.slider(0, 60, value=30, label="keep samples with bpm ≥", show_value=True)
    keep_upper = mo.ui.switch(value=True, label="also require bpm ≤ 230")
    mo.hstack([lower, keep_upper], justify="start", gap=2)
    return keep_upper, lower


@app.cell(hide_code=True)
def _(hr, keep_upper, lower, mo, sv, workouts):
    from ibis import _

    _cond = hr.bpm >= lower.value
    if keep_upper.value:
        _cond = _cond & (hr.bpm <= 230)
    _valid = hr.filter(_cond)
    _expr = _valid.join(
        workouts,
        (_valid.user_id == workouts.user_id) & (_valid.ts >= workouts.start) & (_valid.ts < workouts.end),
    ).select(_valid.user_id, workouts.kind, _valid.ts, _valid.bpm, workouts.start, workouts.end)
    _report = sv.verify(
        _expr,
        requires={"workouts": [_.start.notnull(), _.end.notnull()]},
        ensures=[_.bpm >= 30, _.bpm <= 230, ~_.bpm.isnan()],
    )
    mo.md(_report._repr_markdown_())
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 4. Keep it up to date, incrementally

    New samples arrive every few seconds; recomputing the join each time is
    wasteful. `sv.IncrementalView` asks Lean for **delta plans**: queries
    that compute only the *change* to the result from the changes to the
    inputs. Lean proves that old result + change = new result, for every
    database and every batch of changes.

    The view below starts from the result of `workout_heart_rate`. Stream in
    samples, and log an overlapping workout to see why `unique(user_id, ts)`
    was refused.
    """)
    return


@app.cell
def _(con, expr, sv):
    view = sv.IncrementalView(con, expr, "workout_hr")
    view_log = {"stream": 0, "overlap": 0, "batches": []}  # button presses applied so far
    f"{len(view.deltas)} delta plans, generated and proved by Lean"
    return view, view_log


@app.cell(hide_code=True)
def _(mo):
    stream = mo.ui.button(value=0, on_click=lambda n: n + 1, label="Stream the next two samples", kind="success")
    overlap = mo.ui.button(
        value=0, on_click=lambda n: n + 1, label="Log an overlapping workout (user 1, stretch 07:10–07:20)", kind="warn"
    )
    mo.hstack([stream, overlap], justify="start")
    return overlap, stream


@app.cell(hide_code=True)
def _(t):
    def sample_batch(i):
        """The i-th batch of the simulated stream: one sample per user, with a
        glitch every third batch."""
        minute = 20 + 2 * i
        h, m = 7 + minute // 60, minute % 60
        user2 = 0.0 if i % 3 == 2 else 150.0 + i
        return [(1, t(h, m), 140.0 + 3 * i), (2, t(h, m), user2)]

    return (sample_batch,)


@app.cell(hide_code=True)
def _(overlap, sample_batch, stream, sv, t, view, view_log):
    # Each button press since the last run of this cell becomes one batch.
    _log = view_log
    while _log["stream"] < stream.value:
        _rows = sample_batch(_log["stream"])
        view.apply({"heart_rate": sv.Changes(inserts=_rows)})
        _log["batches"].append(("heart_rate", _rows))
        _log["stream"] += 1
    while _log["overlap"] < overlap.value:
        _row = (1, "stretch", t(7, 10), t(7, 20))
        view.apply({"workouts": sv.Changes(inserts=[_row])})
        _log["batches"].append(("workouts", [_row]))
        _log["overlap"] += 1
    applied = len(_log["batches"])
    return (applied,)


@app.cell(hide_code=True)
def _(applied, mo, view, view_log):
    from collections import Counter as _Counter

    _cols = ["user_id", "kind", "ts", "bpm"]

    def _rows(rows):
        return [dict(zip(_cols, r[:4])) for r in sorted(rows, key=lambda r: (r[0], r[2], r[1]))]

    _dupes = [k for k, n in _Counter((r[0], r[2]) for r in view.rows()).items() if n > 1]
    _equal = view.rows() == view.recompute()
    _last = (
        mo.md("*Press a button to change the inputs.*")
        if not view_log["batches"]
        else mo.md(
            f"Last batch: {len(view_log['batches'][-1][1])} row(s) inserted into "
            f"`{view_log['batches'][-1][0]}`."
        )
    )
    mo.vstack(
        [
            _last,
            mo.hstack(
                [
                    mo.vstack([mo.md("**maintained incrementally**"), mo.ui.table(_rows(view.rows()), selection=None)]),
                    mo.vstack([mo.md("**recomputed from scratch**"), mo.ui.table(_rows(view.recompute()), selection=None)]),
                ],
                justify="start",
                gap=2,
            ),
            mo.callout(
                mo.md(
                    f"After {applied} batch(es) the maintained view "
                    + ("**equals** full recomputation ✓" if _equal else "**differs** ✗")
                    + ". Glitched samples (bpm 0) never enter it: the filter is part of the delta plans."
                ),
                kind="success" if _equal else "danger",
            ),
            mo.callout(
                mo.md(
                    "**`unique(user_id, ts)` is violated** for "
                    + ", ".join(f"user {u} at {ts:%H:%M}" for u, ts in _dupes)
                    + ": the samples fall inside both the run and the stretch. "
                    "This is exactly the input Lean could not rule out."
                ),
                kind="warn",
            )
            if _dupes
            else mo.md(""),
        ],
        gap=1,
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## What is trusted, what is proved

    * **Proved in Lean**: the interval and NULL analysis behind every ✅, the
      key analysis behind `unique`, and that the delta plans compute exactly
      the change to the view. Floats follow DataFusion's semantics bit for
      bit, NaN and −0.0 included.
    * **Trusted**: the translation from DataFusion's Substrait JSON into the
      Lean model, DataFusion itself, and the small amount of Python that
      stores the view and merges changes. The intro notebook
      (`notebooks/intro.py`) explains the formal side step by step.
    """)
    return


if __name__ == "__main__":
    app.run()

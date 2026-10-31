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
app = marimo.App(width="medium", app_title="12. Doubles, time and text")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 11. [Engines and SQL](?file=11_engines.py) · [Contents](?file=00_start_here.py) · 13. [Plans, meaning and proofs](?file=13_plans_and_proofs.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 12. Doubles, time and text

    Integers are the easy case. Real pipelines are full of floating-point
    measurements, timestamps and strings, each with traps of its own. The
    Lean model pins each of them down, bit for bit where it matters, because
    a proof about the wrong semantics proves nothing.

    ## Doubles: NaN, infinities and one zero

    In Python (and in IEEE 754 comparisons) `NaN` is not equal to anything,
    not even itself, and every comparison with it is false. SQL engines
    (PostgreSQL, DuckDB, Spark, Snowflake) do something else, and so does the
    model: doubles are ordered

    > −∞ < … < 0.0 < … < +∞ < NaN

    with **one NaN**, equal to itself and *larger than every number*, and
    **one zero**: IEEE's −0.0 *is* 0.0, so `-0.0 >= 0` holds and −0.0 never
    shows in a result. (DataFusion's own order, `f64::total_cmp`, splits
    both; `sverify` stores DataFusion's tables the model's way, see
    [chapter 16](?file=16_datafusion_semantics.py).) Here it is, live:
    """)
    return


@app.cell
def _():
    import datetime as dt
    import json
    import math

    import ibis
    import sverify as sv
    from sverify.engine import run_sql

    con = sv.connect()
    sv.create_table(
        con,
        "m",
        ibis.schema({"v": "float64"}),
        [(1.5,), (math.nan,), (-1.0,), (0.0,), (-0.0,), (math.inf,), (-9999.0,), (None,)],
    )
    return con, dt, ibis, json, run_sql, sv


@app.cell(hide_code=True)
def _(con, display, run_sql):
    display.arrow(
        run_sql(
            con,
            "select v, v > 0 as positive, v = 'NaN'::double as equals_nan,"
            " v < 'Infinity'::double as below_inf from m order by v",
        ),
        title="the table's doubles, as the model has them",
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Two consequences that bite in practice:

    * **`v > 0` keeps NaN rows.** A filter you meant as "positive readings"
      lets glitches through. Only an upper bound (`v < 1e9`, say) removes NaN.
    * **−0.0 is 0.0**: the table was given both zeros and holds one, so
      `-0.0 >= 0` is TRUE, `DISTINCT` keeps one zero, and `-1 * 0.0` is
      `0.0`, on every engine.

    Lean models doubles exactly, as integer codes in the same order
    (`SubstraitLean/Float.lean`), so the proofs know all of this. Build a
    filter and see whether "no NaN" follows:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    lower = mo.ui.switch(value=True, label="keep v > 0")
    upper = mo.ui.switch(value=False, label="keep v < 1e9")
    no_sentinel = mo.ui.switch(value=False, label="drop the error code v = -9999")
    mo.hstack([lower, upper, no_sentinel], justify="start", gap=2)
    return lower, no_sentinel, upper


@app.cell(hide_code=True)
def _(con, display, lower, mo, no_sentinel, sv, upper):
    from ibis import _

    _m = con.table("m")
    _conds = [
        c
        for c, on in [
            (_m.v > 0, lower.value),
            (_m.v < 1e9, upper.value),
            (_m.v != -9999.0, no_sentinel.value),
        ]
        if on
    ]
    _filtered = _m.filter(*_conds) if _conds else _m
    _report = sv.verify(
        _filtered.select("v"), ensures=[~_.v.isnan(), _.v != -9999.0, _.v.notnull()]
    )
    display.side_by_side(
        mo.md(_report._repr_markdown_()), display.arrow(_filtered, title="kept rows")
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Comparisons with constants are exact, including sentinels like `-9999.0`
    and boundaries like `v > 0.5` versus `v >= 0.5`. Arithmetic on doubles
    (`v * 2.5`) is only known to give "some double", because rounding isn't
    modelled. `FLOOR`, `CEIL`, `ROUND` and the cast to an integer *are*
    exact and monotone, so a bounded double rounds to a bounded integer:
    """)
    return


@app.cell
def _(con, sv):
    from ibis import _

    _m = con.table("m")
    sv.verify(
        _m.filter(_m.v.between(0, 1)).select("v", scaled=_m.v * 2.5, rounded=_m.v.round()),
        ensures=[~_.v.isnan(), _.scaled >= 0, _.rounded >= 0, _.rounded <= 1],
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Timestamps and intervals

    Timestamps are microseconds since 1970 (UTC) in the model; intervals are
    durations. Comparisons with literals, `ts + interval`, `ts1 - ts0` and
    joins on time are all tracked, like integers. The calendar functions are
    computed exactly on the Gregorian calendar (`SubstraitLean/Time.lean`),
    and Lean proves they **grow with the timestamp**, so a range of
    timestamps gives a range of years, of truncated months, and so on.

    Pick a time window and see what Lean derives:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    start = mo.ui.date(value="2024-03-01", label="from")
    end = mo.ui.date(value="2024-04-01", label="until (exclusive)")
    mo.hstack([start, end], justify="start", gap=2)
    return end, start


@app.cell
def _(display, dt, end, ibis, mo, start, sv):
    events = ibis.table({"ts": "timestamp"}, name="events")
    _lo = dt.datetime.combine(start.value, dt.time())
    _hi = dt.datetime.combine(end.value, dt.time())
    _in_window = events.filter(events.ts >= _lo, events.ts < _hi)
    _report = sv.verify(
        _in_window.select(
            "ts",
            year=_in_window.ts.year(),
            hour=_in_window.ts.hour(),
            month_start=_in_window.ts.truncate("M"),
            week_start=_in_window.ts.truncate("W"),
            a_minute_later=_in_window.ts + ibis.interval(minutes=1),
        )
    )
    display.table(
        list(_report.facts.items()), ["column", "what Lean knows"]
    ) if _lo < _hi else mo.md("*Pick an end after the start.*")
    return (events,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Within one calendar year, `year` is that exact integer. Truncations stay
    inside the window's range (rounded down), `hour` is in `[0, 23]` (a
    proved range, not monotone). Without the filter, Lean warns that
    truncating to a month **may fail**: DataFusion can't truncate timestamps
    near the ends of its range (chapter 6 shows how such warnings work).
    """)
    return


@app.cell
def _(events, sv):
    sv.verify(events.select(month_start=events.ts.truncate("M")))
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Text

    Strings are sequences of Unicode characters in the model.
    `substring`, `strpos`, `character_length`, `trim`, `||` and `LIKE` are
    computed exactly, and the test suite checks them against DataFusion on
    random strings. Here is Lean's `Rel.eval` next to DataFusion on some
    awkward words:
    """)
    return


@app.cell
def _(con, display, ibis, json, run_sql, sv):
    from sverify.testing import inline_tables, lean_rows

    sv.create_table(
        con, "w", ibis.schema({"word": "string"}), [("Grüße",), ("naïve ",), ("a%b",), (None,)]
    )
    _sql = (
        "select word, substr(word, 2, 3) as middle, character_length(word) as len,"
        " word like 'a\\%b' as literal_percent, btrim(word) as trimmed, strpos(word, 'ß') as eszett from w"
    )
    _plan = json.loads(sv.substrait_json(con, _sql))
    _cols = _plan["relations"][0]["root"]["names"]
    _lean = lean_rows(json.dumps(inline_tables(_plan, {"w": sv.table_rows(con, "w")})))
    display.side_by_side(
        display.table(_lean, _cols, title="Lean"),
        display.arrow(run_sql(con, _sql), title="DataFusion"),
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    `UPPER`, `LOWER` and regular expressions are **black boxes**: Lean knows
    they return a string (or a boolean), and no proof depends on *which*
    one, because Unicode case mapping and regex engines are big and
    engine-specific. A regular expression is a possible runtime error unless
    Lean can see it compiles: patterns in a conservative subset of Rust's
    syntax are accepted, anything fancier is reported. A back-reference like
    `\1` isn't supported by DataFusion's engine at all:
    """)
    return


@app.cell
def _(con, sv):
    from ibis import _

    _w = con.table("w")
    sv.verify(
        _w.filter(_w.word.notnull()).select(
            n=_w.word.length(),
            shout=_w.word.upper().concat("!"),
            has_digits=_w.word.re_search("[0-9]+"),
            repeated=_w.word.re_search(r"(a|b)\1"),
        ),
        ensures=[_.n >= 0, _.shout.notnull()],
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    String *contents* aren't tracked by contracts yet: `startswith('acc')` in
    a filter doesn't let Lean prove `startswith('ac')` afterwards. Lengths,
    NULLs and errors are.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 11. [Engines and SQL](?file=11_engines.py) · [Contents](?file=00_start_here.py) · 13. [Plans, meaning and proofs](?file=13_plans_and_proofs.py) →
    """)
    return


if __name__ == "__main__":
    app.run()

# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "ibis-framework==12.0.0",
#     "marimo",
#     "sverify==0.2.0",
# ]
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="medium", app_title="6. Runtime errors")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 5. [Keys and relations](?file=05_keys_and_relations.py) · [Contents](?file=00_start_here.py) · 7. [Windows and ASOF joins](?file=07_windows_and_asof.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 6. Runtime errors

    Say you're on call this week. At 3 a.m. a pipeline that was "correct"
    crashes on a row nobody expected, and you're the one it pages. A
    pipeline that quietly writes a wrong number instead is worse: nobody
    gets paged at all.

    Some operations can **fail** in DataFusion, and some silently give a
    **wrong** answer:

    | | operation | what goes wrong |
    |:---|:---|:---|
    | ❌ error | integer `/` or `%` by zero | the query fails |
    | ❌ error | `-9223372036854775808 / -1` | the result doesn't fit in 64 bits; the query fails |
    | ❌ error | `CAST(x AS BIGINT)` of NaN, ±∞ or a huge double (also after `ROUND`) | the query fails |
    | ❌ error | integer `POWER` with a negative exponent or a huge result | the query fails |
    | ❌ error | a regular expression that doesn't compile | the query fails |
    | ❌ error | truncating a timestamp near the ends of its range to a month or year | DataFusion panics or returns garbage |
    | ⚠️ warning | `+`, `-`, `*` leaving 64 bits | DataFusion **wraps around** silently: `2⁶² + 2⁶²` gives `-2⁶³` |

    Lean's model computes with exact (unbounded) integers, and
    `SubstraitLean/Safety.lean` lists, for every operation of a plan, which
    of these can happen. Theorem `Rel.mayIssues_sound` proves the list
    complete: **if the report lists no error, no input can trigger one.**
    `@sv.transform` refuses a transformation that may fail, even with no
    postconditions at all.

    ## Guards, and where DataFusion respects them

    The usual fix is a *guard*: make sure the divisor isn't zero before
    dividing. Whether a guard works depends on **when DataFusion evaluates
    each part**, and that is less obvious than it looks. The table below
    has a row for each kind of trouble: a zero divisor, `MIN` divided by
    `-1`, and doubles a `BIGINT` can't hold. Pick a variant, and we'll
    show Lean's report next to DataFusion actually running it on that
    table.
    """)
    return


@app.cell
def _():
    import ibis
    import sverify as sv
    from sverify.engines import create_table, table_rows
    from sverify.errors import VerificationError

    MIN, MAX = -(2**63), 2**63 - 1

    con = sv.connect()
    create_table(
        con,
        "t",
        ibis.schema({"qty": "int64", "n": "int64", "amount": "float64"}),
        [(7, 2, 3.4), (5, 0, 1e30), (MIN, -1, float("nan")), (MAX, 3, 50.0)],
    )
    t = con.table("t")

    VARIANTS = {
        "qty // n (no guard)": t.select(x=t.qty // t.n),
        "filter n != 0, then select qty % n": t.filter(t.n != 0).select(x=t.qty % t.n),
        "filter n != 0, then select qty // n": t.filter(t.n != 0).select(x=t.qty // t.n),
        "filter n > 0, then select qty // n": t.filter(t.n > 0).select(x=t.qty // t.n),
        "select qty % nullif(n, 0)": t.select(x=t.qty % t.n.nullif(0)),
        "select CASE WHEN n != 0 THEN qty % n ELSE 0 END": t.select(
            x=ibis.cases((t.n != 0, t.qty % t.n), else_=0)
        ),
        "filter (n != 0) AND (qty % n > 1)": t.filter((t.n != 0) & ((t.qty % t.n) > 1)),
        "filter n != 0, then filter qty % n > 1": t.filter(t.n != 0).filter((t.qty % t.n) > 1),
        "select round(amount) (a cast to BIGINT)": t.select(x=t.amount.round()),
        "filter 0 <= amount <= 100, then round(amount)": t.filter(
            (t.amount >= 0) & (t.amount <= 100)
        ).select(x=t.amount.round()),
        "select qty + 1": t.select(x=t.qty + 1),
    }
    return MAX, MIN, VARIANTS, VerificationError, con, sv, table_rows


@app.cell(hide_code=True)
def _(MAX, MIN, con, display, table_rows):
    _shown = [
        tuple("MIN" if v == MIN else "MAX" if v == MAX else v for v in r)
        for r in table_rows(con, "t")
    ]
    display.table(
        _shown,
        ["qty", "n", "amount"],
        title="t   (MIN and MAX are the smallest and largest 64-bit integers)",
    )
    return


@app.cell(hide_code=True)
def _(VARIANTS, mo):
    variant = mo.ui.dropdown(list(VARIANTS), value="qty // n (no guard)", label="pipeline")
    variant
    return (variant,)


@app.cell(hide_code=True)
def _(VARIANTS, display, mo, sv, variant):
    _expr = VARIANTS[variant.value]
    _report = sv.verify(_expr)
    try:
        _ran = display.arrow(_expr, title="DataFusion's result")
    except Exception as _e:
        _ran = mo.callout(
            mo.md(f"**DataFusion fails:** `{str(_e).splitlines()[0][:160]}`"), kind="danger"
        )
    _summary = (
        mo.callout(mo.md("Lean proves this **cannot fail**, on any data."), kind="success")
        if not _report.errors
        else mo.callout(mo.md("Lean **can't rule out** a runtime error."), kind="warn")
    )
    mo.vstack([_summary, display.side_by_side(mo.md(_report._repr_markdown_()), _ran)])
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    What the variants show:

    * **`nullif(n, 0)` and `CASE`** are reliable guards: DataFusion evaluates
      a `CASE` branch only when its condition holds, and `NULLIF` is a `CASE`
      underneath. Lean evaluates each branch *knowing* its condition.
    * **A filter below a projection** works too: the projection only sees
      rows that passed. But `n != 0` doesn't rule out `MIN / -1`, so
      division still may overflow; `n > 0` fixes that.
    * **The same `AND`** is not a guard: DataFusion may evaluate both sides
      of an `AND`, so `qty % n` runs on the `n = 0` row anyway.
    * **An earlier filter** is not a guard either, which surprises
      everyone: DataFusion's optimizer *merges* the two filters into one
      `AND`. Lean models that (`Rel.loose`), so it reports the error, and
      DataFusion indeed fails.
    * **`round(amount)`** becomes a cast to `BIGINT`, which fails on `1e30`
      and NaN. Bounding `amount` first makes it safe, because `ROUND` is
      exact and monotone in the model (`FloatCode.round_mono`).
    * **`qty + 1`** only warns: on `MAX` it wraps around to `MIN`. No
      error, but not the mathematical answer either.

    ## Contracts refuse possible errors

    For whoever is on call, this is the part that matters: a contracted
    transformation must be proved free of runtime errors, not only correct
    when it runs. Warnings (wrap-around) don't block it:
    """)
    return


@app.cell
def _(VerificationError, mo, sv):
    @sv.transform()
    def ratio(t):
        return t.select(x=t.qty // t.n)

    @sv.transform()
    def safe_ratio(t):
        positive = t.filter(t.n > 0)
        return positive.select(x=positive.qty // positive.n)

    import ibis as _ibis

    _t = _ibis.table({"qty": "int64", "n": "int64"}, name="t")
    try:
        ratio(_t)
    except VerificationError as _e:
        _err = str(_e).splitlines()[0]
    safe_ratio(_t)
    mo.vstack(
        [
            mo.callout(mo.md(f"`ratio`: **VerificationError**: {_err}"), kind="danger"),
            mo.callout(mo.md("`safe_ratio`: proved free of runtime errors ✓"), kind="success"),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    `Report.errors` and `Report.warnings` list the issues; `Report.proved` is
    true only when every postcondition is proved **and** there are no errors.

    What's trusted here is the timing: *when* DataFusion evaluates an
    expression (lazy `CASE`, eager `AND`/`OR`, merged filters). The test
    suite runs DataFusion and DuckDB on random data, including the extreme
    values, and checks that they only ever fail where Lean reported an error.

    You can now tell a guard that works from one that only looks like it,
    and a contract refuses any plan that could crash, so the 3 a.m. page
    for a zero divisor never comes. **Next up:**
    [Windows and ASOF joins](?file=07_windows_and_asof.py), where each row
    looks at its neighbours.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 5. [Keys and relations](?file=05_keys_and_relations.py) · [Contents](?file=00_start_here.py) · 7. [Windows and ASOF joins](?file=07_windows_and_asof.py) →
    """)
    return


if __name__ == "__main__":
    app.run()

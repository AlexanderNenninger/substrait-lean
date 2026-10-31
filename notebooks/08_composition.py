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
app = marimo.App(width="medium", app_title="8. Composing contracts")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 7. [Windows and ASOF joins](?file=07_windows_and_asof.py) · [Contents](?file=00_start_here.py) · 9. [Incremental views](?file=09_incremental_views.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 8. Composing contracts

    Say the billing team owns a step that cleans up `orders`, and you own the
    step after it that doubles the amounts for a promotion. You've never read
    their code, and you shouldn't have to. What you rely on is their
    contract. If each step has one, the contracts should **compose**: when
    one step's output feeds another, the downstream step's preconditions
    should follow from what the upstream step guarantees, with no need to
    check the intermediate data.

    That is exactly what happens. When the input of a contracted function is
    the result of another contracted function, `sverify`:

    1. **proves** the downstream preconditions from the upstream contract
       (they are never checked on data), and
    2. proves the downstream postconditions assuming **only** what the
       upstream step guarantees, not what its code happens to do.

    ## Two steps that fit together
    """)
    return


@app.cell
def _():
    import ibis
    import sverify as sv
    from ibis import _

    orders = ibis.table({"id": "int64", "customer": "string", "amount": "int64"}, name="orders")

    @sv.transform(
        requires={"orders": [_.amount >= 0, sv.unique("id")]},
        ensures=[_.amount >= 0, _.amount.notnull(), sv.unique("id")],
    )
    def paid(orders):
        """Orders with a known amount."""
        return orders.filter(orders.amount.notnull())

    @sv.transform(
        requires={"t": [_.amount >= 0, _.amount.notnull()]},
        ensures=[_.doubled >= 0, _.doubled.notnull()],
    )
    def doubled(t):
        return t.select(t.id, t.customer, doubled=t.amount * 2)

    doubled(paid(orders))
    doubled.last_report
    return doubled, ibis, orders, paid, sv


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The `requires paid: …` rows say what `doubled` was allowed to assume: the
    guarantees of `paid`, not facts about `orders`. Each link is a **Hoare
    triple**, the classic notation of program verification: `{P} f {Q}`
    means "if `P` holds before `f`, then `Q` holds after". The rule

    > `{P} g {Q}` and `{Q} f {S}` give `{P} f ∘ g {S}`

    is theorem `Triple.compose` in `SubstraitLean/Compose.lean`.

    ## When the link breaks

    Now let's swap the team upstream for someone who promises less. Pick
    what feeds `doubled`:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    upstream = mo.ui.radio(
        {
            "paid (guarantees amount ≥ 0 and not NULL)": "paid",
            "not_null (guarantees only that amount is not NULL)": "not_null",
            "a plain Ibis filter: amount > 0": "plain",
            "a plain Ibis filter: amount IS NOT NULL": "plain_notnull",
        },
        value="not_null (guarantees only that amount is not NULL)",
        label="upstream step",
    )
    upstream
    return (upstream,)


@app.cell
def _(doubled, mo, orders, paid, sv, upstream):
    from ibis import _

    @sv.transform(ensures=[_.amount.notnull()])
    def not_null(orders):
        return orders.filter(orders.amount.notnull())

    _inputs = {
        "paid": lambda: paid(orders),
        "not_null": lambda: not_null(orders),
        "plain": lambda: orders.filter(orders.amount > 0),
        "plain_notnull": lambda: orders.filter(orders.amount.notnull()),
    }
    try:
        doubled(_inputs[upstream.value]())
        _out = mo.vstack(
            [mo.callout(mo.md("Every link holds ✓"), kind="success"), doubled.last_report]
        )
    except sv.CompositionError as _e:
        _out = mo.callout(mo.md(f"**CompositionError**: {str(_e).splitlines()[0]}"), kind="danger")
    except sv.VerificationError as _e:
        _out = mo.callout(mo.md(f"**VerificationError**: {str(_e).splitlines()[0]}"), kind="danger")
    _out
    return (not_null,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    * **`not_null`** guarantees too little: `doubled` needs `amount ≥ 0`, and
      nothing upstream promises it. The error names both sides of the
      broken link. (`not_null`'s own code would happen to keep negative
      amounts, but that's beside the point: only the contract counts.)
    * **A plain Ibis step** carries no contract of its own. What follows from
      its operations is still proved: `amount > 0` implies both of
      `doubled`'s preconditions. With only `amount IS NOT NULL`, the
      missing `amount ≥ 0` is treated like a precondition on a base table:
      checked on the data if there is data, assumed otherwise. That's why
      that choice goes through here.
    * A precondition can also follow from more than the upstream `ensures`:
      it is proved as an extra postcondition of the upstream function, from
      that function's own preconditions. Keys (`sv.unique`) propagate the
      same way.

    ## On real data

    With bound tables, only the **base** tables are checked: `paid`'s
    preconditions on `orders`. The intermediate result is never inspected;
    `doubled`'s preconditions were proved. Here are three well-behaved
    orders, including cy's free one:
    """)
    return


@app.cell
def _(display, doubled, ibis, mo, paid, sv):
    con = sv.connect()
    sv.create_table(
        con,
        "orders",
        ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
        [(1, "ada", 30), (2, "bob", 5), (3, "cy", 0)],
    )
    _result = doubled(paid(con.table("orders")))
    mo.vstack(
        [
            display.arrow(_result, title="doubled(paid(orders))"),
            mo.md("Now add an order that breaks `paid`'s precondition:"),
        ]
    )
    return (con,)


@app.cell
def _(con, doubled, ibis, mo, paid, sv):
    sv.create_table(
        con,
        "bad_orders",
        ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
        [(1, "ada", 30), (1, "dee", 12)],
    )
    try:
        doubled(paid(con.table("bad_orders")))
    except sv.PreconditionError as _e:
        _err = _e
    mo.callout(mo.md(f"**PreconditionError** from `paid`: {_err}"), kind="danger")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Where did a result come from?

    When the analyst downstream asks why they can trust a number, you'll
    want to say what it rests on. `sverify.contracts.provenance(expr)` shows
    what a contracted result assumed and what it guarantees: `guarantees`
    are its proved postconditions, `external` the preconditions on base
    tables that the whole chain rests on.
    """)
    return


@app.cell
def _(display, doubled, mo, orders, paid):
    from sverify.contracts import label, provenance

    _p = provenance(doubled(paid(orders)))
    mo.vstack(
        [
            display.table([[label(c)] for c in _p.guarantees], ["guarantees"]),
            display.table(
                [[t, label(c)] for t, cs in _p.external.items() for c in cs],
                ["base table", "assumed"],
            ),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Orders keep arriving, so composed results also need to be **kept up to
    date**: chapter 10 maintains `doubled(paid(orders))` incrementally, and
    shows how its guarantees keep holding while the data changes.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 7. [Windows and ASOF joins](?file=07_windows_and_asof.py) · [Contents](?file=00_start_here.py) · 9. [Incremental views](?file=09_incremental_views.py) →
    """)
    return


if __name__ == "__main__":
    app.run()

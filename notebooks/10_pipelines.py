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
app = marimo.App(width="medium", app_title="10. Pipelines")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 9. [Incremental views](?file=09_incremental_views.py) · [Contents](?file=00_start_here.py) · 11. [Engines and SQL](?file=11_engines.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 10. Pipelines

    Real pipelines are layered: cleaned tables feed joined tables feed
    reports. `sv.Pipeline` maintains several views that **read each other**.
    Each view's change is handed to the views that read it, so an
    intermediate result is computed once and shared, and only changes flow
    through the layers.

    This chapter brings chapters 8 and 9 together: the base layer is the
    contracted `doubled(paid(orders))`, and its guarantees keep holding in
    **every** state of the pipeline, not just the first.

    ## Three layers
    """)
    return


@app.cell
def _():
    import ibis
    import sverify as sv
    from ibis import _

    @sv.transform(
        requires={"orders": [_.amount >= 0, sv.unique("id")]},
        ensures=[_.amount >= 0, _.amount.notnull(), sv.unique("id")],
    )
    def paid(orders):
        return orders.filter(orders.amount.notnull())

    @sv.transform(
        requires={"t": [_.amount >= 0, _.amount.notnull()]},
        ensures=[_.doubled >= 0, _.doubled.notnull()],
    )
    def doubled(t):
        return t.select(t.id, t.customer, doubled=t.amount * 2)

    con = sv.connect()
    sv.create_table(
        con,
        "orders",
        ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
        [(1, "ada", 30), (2, "bob", 5), (3, "cy", 0)],
    )
    sv.create_table(
        con,
        "customers",
        ibis.schema({"name": "string", "city": "string"}),
        [("ada", "Paris"), ("cy", "Lima")],
    )

    pipe = sv.Pipeline(con)
    base = pipe.view("base", doubled(paid(con.table("orders"))))
    b, customers = base.table, con.table("customers")
    pipe.view(
        "cities", b.join(customers, b.customer == customers.name).select("id", "city", "doubled")
    )
    pipe.view("located", b.left_join(customers, b.customer == customers.name).select("id", "city"))
    pipe.fallbacks
    return base, pipe, sv


@app.cell(hide_code=True)
def _(mo):
    mo.mermaid(
        """
        graph BT
          O["orders"] --> B["base<br/>doubled(paid(orders))"]
          B --> C["cities<br/>inner join customers"]
          B --> L["located<br/>left join customers<br/>(recomputed)"]
          K["customers"] --> C
          K --> L
          style B fill:#d4f4dd,stroke:#2e8b57
        """
    )
    return


@app.cell(hide_code=True)
def _(base, mo):
    from sverify.contracts import label

    mo.md(
        "* A view reads base tables and earlier views (`view.table`). A "
        "contracted transformation applied to `view.table` builds on that view's "
        "guarantees, as in a direct composition.\n"
        "* `pipe.fallbacks` (the output above) lists views without update rules: "
        "`located` is a left join, so it is **recomputed and diffed** on each batch. "
        "Its change still flows to any view downstream.\n"
        f"* `base.guarantees` = `{', '.join(label(g) for g in base.guarantees)}`: what holds "
        f"in every state. `base.requires` = `{'; '.join(f'{t}: {label(c)}' for t, cs in base.requires.items() for c in cs)}`: "
        "what every batch is checked against."
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Changes, layer by layer

    Each button applies one batch to `orders` and `customers`. Two of them
    break a precondition of `paid`:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    good = mo.ui.button(
        value=0, on_click=lambda n: n + 1, label="New orders and a new customer", kind="success"
    )
    dup = mo.ui.button(
        value=0,
        on_click=lambda n: n + 1,
        label="Insert an order with an existing id",
        kind="danger",
    )
    neg = mo.ui.button(
        value=0,
        on_click=lambda n: n + 1,
        label="Insert an order with a negative amount",
        kind="danger",
    )
    mo.hstack([good, dup, neg], justify="start")
    return dup, good, neg


@app.cell(hide_code=True)
def _():
    # Button presses applied so far, and what the last one did.
    presses = {"good": 0, "dup": 0, "neg": 0, "last": None}
    return (presses,)


@app.cell(hide_code=True)
def _(dup, good, neg, pipe, presses, sv):
    _cities = ["Oslo", "Rome", "Lima", "Paris"]

    def _try(kind, changes):
        try:
            pipe.apply(changes)
            presses["last"] = (kind, None)
        except sv.PreconditionError as e:
            presses["last"] = (kind, str(e))

    while presses["good"] < good.value:
        _i = presses["good"]
        _try(
            "good",
            {
                "orders": sv.Changes(inserts=[(10 + _i, "bob", 3 * _i), (20 + _i, f"new{_i}", 7)]),
                "customers": sv.Changes(inserts=[(f"new{_i}", _cities[_i % 4])]),
            },
        )
        presses["good"] += 1
    while presses["dup"] < dup.value:
        _try("dup", {"orders": sv.Changes(inserts=[(1, "dee", 4)])})
        presses["dup"] += 1
    while presses["neg"] < neg.value:
        _try("neg", {"orders": sv.Changes(inserts=[(99, "eve", -5)])})
        presses["neg"] += 1
    state = (presses["good"], presses["dup"], presses["neg"])
    return (state,)


@app.cell(hide_code=True)
def _(display, mo, pipe, presses, state):
    _ = state
    _views = pipe.views
    _last = presses["last"]
    if _last is None:
        _msg = mo.md("*Press a button.*")
    elif _last[1] is None:
        _msg = mo.callout(mo.md("Batch applied to every layer."), kind="success")
    else:
        _msg = mo.callout(
            mo.md(f"**PreconditionError**: {_last[1]}. The batch was refused; nothing changed."),
            kind="danger",
        )
    _equal = all(v.rows() == v.recompute() for v in _views.values())
    mo.vstack(
        [
            _msg,
            display.side_by_side(
                *[
                    display.table(sorted(v.rows(), key=lambda r: r[0]), v.columns, title=name)
                    for name, v in _views.items()
                ]
            ),
            display.verdict(
                _equal,
                "Every view equals its full recomputation ✓",
                "A view differs from its recomputation ✗",
            ),
        ],
        gap=1,
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Why the guarantees survive every batch

    `paid`'s preconditions were checked on all of `orders` once, when the
    pipeline was built. After that, only **the batch** is checked:

    * row conditions (`amount >= 0`) on the inserted rows;
    * keys (`unique(id)`) among the inserted rows and against the keys of
      the rows the batch keeps.

    That is enough, by theorem `Spec.update` in `SubstraitLean/Compose.lean`:
    a table's contract survives a batch if the inserted rows satisfy the row
    conditions and their keys clash with neither each other nor the kept
    rows. `Triple.maintained` then says a contracted view's guarantees hold
    in the new state. So `base` satisfies `doubled ≥ 0` and is non-NULL
    after every batch, without ever re-checking the whole table.

    The layering itself is `Rel.chain_sound` (DBSP's *chain rule*): when a
    view reads another view's stored result, and gets that view's change as
    its change table, its own update plan is still correct. For a recomputed
    view, `ZSet.diff_correct` shows `new − old` is a valid change to pass
    on.

    `sv.IncrementalView` is a pipeline with a single view; on its own it
    refuses queries without update rules, since there's nothing to recompute
    for.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 9. [Incremental views](?file=09_incremental_views.py) · [Contents](?file=00_start_here.py) · 11. [Engines and SQL](?file=11_engines.py) →
    """)
    return


if __name__ == "__main__":
    app.run()

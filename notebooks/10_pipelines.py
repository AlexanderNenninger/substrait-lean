# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "ibis-framework==12.0.0",
#     "marimo",
#     "sverify[delta]",
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

    Say you own the Monday report the sales team presents. It reads orders
    by city, which read the cleaned orders, which read the raw `orders`
    feed, and a bad row anywhere below ends up on their slides.

    Real pipelines are layered like that: cleaned tables feed joined tables
    feed reports. In `sverify` the layers are transforms composed directly,
    each piped from the one below, so the code reads in the order the data
    flows: `orders.pipe(paid).pipe(doubled)` is the same node as the call
    form `doubled(paid(orders))`. The other inputs of a layer come by
    keyword, as `base.pipe(cities, customers=customers)`. Without a `.write` in between they
    **fuse** into one plan, maintained as one incremental view (chapter 9).
    `.write(sink)` **stores** a layer, as a cache in the middle of a job or
    as its output; the layers above read the stored table as a versioned
    source, through its change feed. So an intermediate result is computed
    once and shared, and only changes flow through the layers.

    This chapter brings chapters 8 and 9 together: the base layer is the
    contracted `orders.pipe(paid).pipe(doubled)`, and its guarantees keep holding in
    **every** state of the pipeline, not only the first.

    ## Three layers
    """)
    return


@app.cell
def _():
    import tempfile
    from pathlib import Path

    import pyarrow as pa
    import sverify as sv
    from ibis import _
    from sverify.io import DeltaSink, StaticSource

    lake = Path(tempfile.mkdtemp())  # a local "lake"; any Delta URI works, with storage_options

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

    @sv.transform(requires={"base": [_.doubled.notnull()]}, ensures=[_.doubled.notnull()])
    def cities(base, customers):
        return base.join(customers, base.customer == customers.name).select("id", "city", "doubled")

    @sv.transform()
    def located(base, customers):
        return base.left_join(customers, base.customer == customers.name).select("id", "city")

    def arrow_table(schema, rows):
        return pa.Table.from_pylist([dict(zip(schema.names, r)) for r in rows], schema=schema)

    orders = StaticSource(
        arrow_table(
            pa.schema({"id": pa.int64(), "customer": pa.string(), "amount": pa.int64()}),
            [(1, "ada", 30), (2, "bob", 5), (3, "cy", 0)],
        ),
        name="orders",
    )
    customers = StaticSource(
        arrow_table(
            pa.schema({"name": pa.string(), "city": pa.string()}),
            [("ada", "Paris"), ("cy", "Lima")],
        ),
        name="customers",
    )

    base = orders.pipe(paid).pipe(doubled).write(DeltaSink(str(lake / "base")))
    by_city = base.pipe(cities, customers=customers)
    by_location = base.pipe(located, customers=customers)
    monday = sv.group(by_city, by_location)
    print(monday.refresh())
    return base, by_city, by_location, customers, monday, orders, sv


@app.cell(hide_code=True)
def _(mo):
    mo.mermaid(
        """
        graph BT
          O["orders"] --> B["base (Delta table)<br/>orders.pipe(paid).pipe(doubled), one fused plan"]
          B --> C["cities<br/>inner join customers"]
          B --> L["located<br/>left join customers<br/>(recomputed)"]
          K["customers"] --> C
          K --> L
          style B fill:#d4f4dd,stroke:#2e8b57
        """
    )
    return


@app.cell(hide_code=True)
def _(base, mo, monday):
    mo.md(
        "* `paid` and `doubled` have no `.write` between them, so they fuse into "
        "one plan; `.write(DeltaSink(...))` stores the result as `base`. `cities` and "
        "`located` read `base`'s Delta table, not `orders`.\n"
        "* A contracted transform piped from a stored node builds on what that node's "
        "plan proved, as in a direct composition: `cities` requires "
        "`_.doubled.notnull()` of `base`, which `doubled` guarantees, so it is "
        "checked once, when the node is built, and never on the data. A precondition "
        "`base` doesn't guarantee raises `CompositionError` right there.\n"
        "* `sv.group(by_city, by_location)` refreshes both reports against the same source versions; "
        "`base` is refreshed and written once for the two of them, upstream first. "
        "Its first refresh checked `paid`'s preconditions on all of `orders` "
        "(the `requires … (checked on data)` lines above).\n"
        "* `located` is a left join, so it is **recomputed and diffed** on each "
        "refresh (chapter 9). Its change would still flow to any node reading it. "
        f"`status()` says so:\n\n```text\n{monday.status()}\n{base.status()}\n```"
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Changes, layer by layer

    We'll feed the pipeline. Each button changes `orders` and `customers`
    and refreshes both reports. The first is valid; the other two each
    insert an order that breaks a precondition of `paid`. We refresh with
    `audit=True`, so every batch is also compared with recomputation
    before it is applied (`AuditError` otherwise).
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
def _(customers, dup, good, monday, neg, orders, presses, sv):
    from sverify.errors import PreconditionError

    _cities = ["Oslo", "Rome", "Lima", "Paris"]

    def _try(kind, changes):
        orders.apply(changes["orders"])
        if "customers" in changes:
            customers.apply(changes["customers"])
        try:
            presses["last"] = (kind, str(monday.refresh(audit=True)))
        except PreconditionError as e:
            presses["last"] = (kind, e)
            # The demo takes the bad order out of the feed again, so the
            # next batch can go through.
            orders.apply(sv.Changes(deletes=changes["orders"].inserts))

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
def _(base, by_city, by_location, display, mo, presses, state):
    _ = state
    _last = presses["last"]
    if _last is None:
        _msg = mo.md("*Press a button.*")
    elif isinstance(_last[1], str):
        _msg = mo.vstack(
            [
                mo.callout(
                    mo.md("Batch applied to every layer; the audit found no difference."),
                    kind="success",
                ),
                mo.md(f"`refresh(audit=True)` reports:\n\n```text\n{_last[1]}\n```"),
            ]
        )
    else:
        _msg = mo.callout(
            mo.md(
                f"**PreconditionError**: {_last[1]}. The refresh was refused; no layer "
                "changed and nothing was written."
            ),
            kind="danger",
        )

    def _rows(node):
        return sorted((tuple(r.values()) for r in node.to_arrow().to_pylist()), key=repr)

    mo.vstack(
        [
            _msg,
            display.side_by_side(
                *[
                    display.table(_rows(n), list(n.schema), title=n.name)
                    for n in [base, by_city, by_location]
                ]
            ),
        ],
        gap=1,
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Why the guarantees survive every batch

    Whoever reads `base` relies on its guarantees on the hundredth batch as
    much as on the first. `paid`'s preconditions were checked on all of
    `orders` once, on the first refresh. After that, only **the batch** is
    checked:

    * row conditions (`amount >= 0`) on the inserted rows;
    * keys (`unique(id)`) among the inserted rows and against the keys of
      the rows the batch keeps.

    That is enough, by theorem `Spec.update` in `SubstraitLean/Compose.lean`:
    a table's contract survives a batch if the inserted rows satisfy the row
    conditions and their keys clash with neither each other nor the kept
    rows. `Triple.maintained` then says a contracted view's guarantees hold
    in the new state. So `base` satisfies `doubled ≥ 0` and is non-NULL
    after every batch, without ever re-checking the whole table, and the
    Delta table it is written to records those guarantees with every
    version, for the layers that read it.

    The layering itself is `Rel.chain_sound` (DBSP's *chain rule*): when a
    view reads another view's stored result, and gets that view's change as
    its change table (here, through the Delta change feed), its own update
    plan is still correct. For a recomputed view, `ZSet.diff_correct` shows
    `new − old` is a valid change to pass on.

    Each refresh brings the layers up to date upstream first and writes
    every stored node exactly once per state. If the job stops and
    restarts, building the same nodes again is enough: the first refresh
    resumes each stored node from its table when the plan and the source
    versions match, rather than computing it again.

    You can now stack transforms into layers that pass only their changes
    along, store the ones others read, and rely on every contract's
    guarantees in every state while only the batch is checked. Next up,
    [Engines and SQL](?file=11_engines.py) runs the same checked plans on
    Polars and DataFusion, and as SQL for Snowflake and Spark.
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

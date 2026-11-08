# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "ibis-framework==12.0.0",
#     "marimo",
#     "sverify[datafusion,delta,polars]",
# ]
#
# [tool.uv.sources]
# sverify = { path = "../python", editable = true }
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="compact", app_title="5. Pipelines and engines")


@app.cell(hide_code=True)
def _():
    import datetime as dt
    import json
    import math

    import ibis
    import marimo as mo
    import pyarrow as pa
    import sverify as sv
    from sverify import display

    return dt, display, ibis, json, math, mo, pa, sv


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 4. [Contracts](?file=04_contracts.py)
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 5. Pipelines and engines

    Say the Monday report the sales team presents reads orders by city,
    which read the cleaned orders, which read the raw `orders` feed. A few
    hundred orders change every hour, and a bad row anywhere below ends up
    on their slides. Recomputing every layer each time is slow, and
    hand-written incremental logic ("process the rows where `updated_at` is
    newer than…") misses deletes and late rows until the analyst finds
    totals that no longer add up. Next quarter the platform team also wants
    the job on another engine.

    We'll keep a join up to date from its changes alone, stack transforms
    into layers that pass only their changes along, run the same checked
    plans on several engines, and look at how the model treats doubles,
    time and text.

    ## Keeping a join up to date

    Incremental view maintenance computes the change to a result from the
    changes to its inputs. A source piped into a transform is a node, and
    `node.refresh()` keeps it up to date with update rules proved in Lean.
    We write the query once, as an Ibis transform, pipe one source into it
    and pass the other by keyword. The sources are in-memory tables
    (`StaticSource`, from `sverify.io`); Delta and Iceberg tables work the
    same way (chapter 1 reads a Delta table).
    """)
    return


@app.cell
def _(pa, sv):
    from sverify.engines import delta_plans
    from sverify.io import StaticSource

    def arrow_table(schema, rows):
        return pa.Table.from_pylist([dict(zip(schema.names, r)) for r in rows], schema=schema)

    orders = StaticSource(
        arrow_table(
            pa.schema({"id": pa.int64(), "customer": pa.string(), "amount": pa.int64()}),
            [(1, "ada", 30), (2, "bob", 5), (3, "ada", None)],
        ),
        name="orders",
    )
    customers = StaticSource(
        arrow_table(
            pa.schema({"name": pa.string(), "city": pa.string()}),
            [("ada", "Paris"), ("bob", "Oslo")],
        ),
        name="customers",
    )

    @sv.transform()
    def orders_with_city(o, c):
        return o.join(c, o.customer == c.name).select(o.id, c.city)

    view = orders.pipe(orders_with_city, c=customers)  # plans run on DuckDB by default
    view.refresh()
    view.to_pandas()
    return (
        StaticSource,
        arrow_table,
        customers,
        delta_plans,
        orders,
        orders_with_city,
        view,
    )


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    `orders.apply(sv.io.Changes(inserts=[...], deletes=[...]))` changes a
    source and gives it a new version. The next `view.refresh()` receives
    that change and updates the view from it. To check, we build the same
    node again and refresh it, which computes its result from scratch.
    The button changes both tables at once, at random:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    apply_batch = mo.ui.button(
        value=0, on_click=lambda n: n + 1, label="Apply a random batch of changes", kind="success"
    )
    apply_batch
    return (apply_batch,)


@app.cell(hide_code=True)
def _(apply_batch, customers, display, mo, orders, orders_with_city, sv, view):
    import random as _random

    def _rows(table):
        return sorted((tuple(r.values()) for r in table.to_pylist()), key=repr)

    def _batch(rng, source, make_row):
        current = _rows(source.table)
        deletes = rng.sample(current, k=min(len(current), rng.randint(0, 2)))
        changes = sv.io.Changes(
            inserts=[make_row(rng) for _ in range(rng.randint(0, 2))], deletes=deletes
        )
        source.apply(changes)
        return changes

    def _changes_table(ch, cols, title):
        rows = [list(r) for r in [*ch.inserts, *ch.deletes]]
        return display.table(rows, cols, [1] * len(ch.inserts) + [-1] * len(ch.deletes), title)

    _names = ["ada", "bob", "cy", None]
    _last, _report = None, None
    if apply_batch.value:
        _rng = _random.Random(apply_batch.value)
        _last = {
            "orders": _batch(
                _rng,
                orders,
                lambda r: (r.randint(1, 9), r.choice(_names), r.choice([None, 5, 30, 50])),
            ),
            "customers": _batch(
                _rng, customers, lambda r: (r.choice(_names), r.choice(["Paris", "Oslo", "Lima"]))
            ),
        }
        _report = view.refresh()

    _fresh = orders.pipe(orders_with_city, c=customers)
    _fresh.refresh()
    _maintained, _recomputed = _rows(view.to_arrow()), _rows(_fresh.to_arrow())
    _equal = _maintained == _recomputed
    mo.vstack(
        [
            mo.md("*Press the button to change both tables at once.*")
            if _last is None
            else mo.vstack(
                [
                    display.side_by_side(
                        _changes_table(
                            _last["orders"], ["id", "customer", "amount"], "changes to orders"
                        ),
                        _changes_table(
                            _last["customers"], ["name", "city"], "changes to customers"
                        ),
                    ),
                    mo.md(f"`view.refresh()` reports:\n\n```text\n{_report}\n```"),
                ]
            ),
            display.side_by_side(
                display.table(_maintained, ["id", "city"], title="maintained view"),
                display.table(_recomputed, ["id", "city"], title="recomputed from scratch"),
            ),
            mo.callout(
                mo.md(
                    f"After {apply_batch.value} batch(es) the maintained view "
                    + ("equals full recomputation" if _equal else "differs from it")
                    + ". Each batch runs the Lean-generated update plan on DuckDB as one query."
                ),
                kind="success" if _equal else "danger",
            ),
        ],
        gap=1,
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### What is maintained, and what is recomputed

    Filters, computed columns, inner joins (self-joins too), cross joins,
    semi and anti joins on equal keys, `UNION ALL`, `ORDER BY` and
    `DISTINCT` are maintained from their changes, and so are `COUNT`, exact
    `SUM` and `AVG`, `MIN` and `MAX` per group. Other aggregates recompute
    only the groups a batch touches, windows that share one `PARTITION BY`
    the partitions it touches (for inputs without ties), and bounded `RANGE`
    frames the frames it touches. Left joins (a left join's NULL-padded rows
    must be retracted when a match turns up later), `LIMIT` (it depends on
    row order) and the rest are recomputed and diffed on every refresh
    ([the guide](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/guide.md#nodes-composing-storing-refreshing)). Contracts work on all of them, and the result is
    correct; a recomputed node costs a full run per refresh. `node.status()`
    says which kind of node you have:
    """)
    return


@app.cell(hide_code=True)
def _(customers, mo, orders, orders_with_city, sv):
    @sv.transform()
    def first_two(o):
        return o.limit(2)

    @sv.transform()
    def located(o, c):
        return o.left_join(c, o.customer == c.name).select(o.id, c.city)

    @sv.transform()
    def distinct_orders(o):
        return o.distinct()

    @sv.transform()
    def totals(o):
        return o.group_by("customer").aggregate(total=o.amount.sum())

    KINDS = {
        "the inner join above": lambda: orders.pipe(orders_with_city, c=customers),
        "orders.limit(2)": lambda: orders.pipe(first_two),
        "a left join": lambda: orders.pipe(located, c=customers),
        "orders.distinct()": lambda: orders.pipe(distinct_orders),
        "total amount per customer": lambda: orders.pipe(totals),
    }
    kind = mo.ui.dropdown(list(KINDS), value="a left join", label="query")
    kind
    return KINDS, kind, located


@app.cell(hide_code=True)
def _(KINDS, kind, mo):
    _node = KINDS[kind.value]()
    _node.refresh()
    _status = _node.status()
    mo.callout(
        mo.md(f"`node.status()`: {_status}"),
        kind="info" if _status.nodes[0].recomputed else "success",
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    A recomputed node's change, the difference between its new and its old
    result, still flows to the nodes that read it. The view is a table like
    any other: `view.table` is an Ibis table to query further, and
    `to_arrow()`, `to_polars()` and `to_pandas()` return its rows. Nodes
    are built from Ibis transforms, or from a SQL string with `sv.sql(query)`
    ([the guide](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/guide.md#nodes-composing-storing-refreshing)).

    ### Delta rules in brief

    Every row carries a weight: `+1` for an inserted row, `-1` for a
    deleted one, and an update is a delete plus an insert. A table with
    weights is a Z-set, and adding a batch of changes means summing the
    weights per row. Filter and project treat each row on its own, so
    their change is the same query run on the changes only (theorem
    `Rel.zeval_add`).

    A join pairs rows from two tables. If both change, the new result has
    four kinds of pairs:

    | | old customers `B` | new customers `ΔB` |
    |:---|:---|:---|
    | old orders `A` | `A × B`: in the old result | `A × ΔB`: new |
    | new orders `ΔA` | `ΔA × B`: new | `ΔA × ΔB`: new |

    The change to the join is `ΔA × B + ΔA × ΔB + A × ΔB`. Hand-written
    pipelines often forget the corner term. We'll apply the changes
    "delete order 1, update order 2 from 5 to 20, insert order 4" to the
    orders, and "insert `cy`, delete `bob`" to the customers, with the
    corner term on and off:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    include_corner = mo.ui.switch(value=True, label="include the ΔA × ΔB term")
    include_corner
    return (include_corner,)


@app.cell(hide_code=True)
def _(display, include_corner, mo):
    # A small mirror of SubstraitLean/Incremental.lean: Z-sets are lists of (row, weight).
    def z_lift(rows):
        return [(r, 1) for r in rows]

    def z_join(a, b):
        # orders.customer ($1) = customers.name ($3); NULL never matches
        return [(x + y, w * v) for x, w in a for y, v in b if x[1] is not None and x[1] == y[0]]

    def consolidate(z):
        totals = {}
        for r, w in z:
            totals[tuple(r)] = totals.get(tuple(r), 0) + w
        return sorted(((list(r), w) for r, w in totals.items() if w != 0), key=repr)

    _A = z_lift([[1, "ada", 30], [2, "bob", 5], [3, "ada", None]])
    _dA = [
        ([1, "ada", 30], -1),
        ([2, "bob", 5], -1),
        ([2, "bob", 20], +1),
        ([4, "cy", 50], +1),
    ]
    _B = z_lift([["ada", "Paris"], ["bob", "Oslo"]])
    _dB = [(["cy", "Lima"], +1), (["bob", "Oslo"], -1)]
    _delta = z_join(_dA, _B) + z_join(_A, _dB) + (z_join(_dA, _dB) if include_corner.value else [])
    _incremental = consolidate(z_join(_A, _B) + _delta)
    _recomputed = consolidate(z_join(_A + _dA, _B + _dB))
    _cols = ["id", "customer", "amount", "name", "city"]
    mo.vstack(
        [
            display.side_by_side(
                display.zset(_incremental, _cols, "incremental (old join + delta)"),
                display.zset(_recomputed, _cols, "recomputed from scratch"),
            ),
            display.verdict(
                _incremental == _recomputed,
                "Equal.",
                "Different: rows are missing or have the wrong weight.",
            ),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    With the switch off, the pair "order 4 and customer `cy`" is missing,
    since both are new and only the corner term produces it. Phantom `bob`
    rows appear too, one with weight `-1`: the updated order 2 was paired
    with the old `bob`, and only the corner term cancels that pairing with
    `bob`'s deletion.

    Lean proves the full rule once. `Rel.delta` generates the update plan
    as an ordinary plan that reads the old tables and the change tables,
    and `Rel.delta_correct` proves it computes exactly the change. Any
    engine can run it. `sverify.engines.delta_plans(view.internal_plan)` returns the
    plan of our view. `orders$delta` and `customers$delta` are the change
    tables, with a trailing `__weight` column; old tables get weight 1
    (`Project +[1]`), and the join multiplies weights (`$3 * $6`):
    """)
    return


@app.cell(hide_code=True)
def _(delta_plans, mo, view):
    import subprocess

    from sverify.engine import checker_path

    def _tree(plan):
        out = subprocess.run(
            [str(checker_path()), "/dev/stdin"],
            input=plan,
            capture_output=True,
            text=True,
            check=False,
        ).stdout
        return out.split("tables:")[0].rstrip()

    mo.hstack(
        [mo.md(f"```text\n{_tree(p)}\n```") for p in delta_plans(view.internal_plan)],
        justify="start",
        wrap=True,
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    On each refresh, `substrait-check --delta` builds the update plan
    (`Rel.delta`) and encodes each row's weight as the `__weight` column
    (`Rel.weighted`, with `Rel.weighted_eval` covering an ordinary engine).
    Sverify registers the change tables, runs the plan as one query, sums the weights
    per row and merges the result into the view. A batch is computed
    completely before anything is replaced, so a failure changes nothing.
    A change that can't happen, such as deleting a row that doesn't exist,
    is refused by the source, and neither the source nor the view moves:
    """)
    return


@app.cell
def _(mo, orders, sv, view):
    _before = orders.version, view.versions
    try:
        orders.apply(sv.io.Changes(inserts=[(7, "ada", 70)], deletes=[(99, "nobody", 1)]))
    except ValueError as _e:
        _err = _e
    mo.callout(
        mo.md(
            f"`ValueError`: {_err}. `orders` is still at version {orders.version}, "
            f"and the view still reflects {view.versions}: "
            f"{(orders.version, view.versions) == _before}."
        ),
        kind="warn",
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The theorems cover the Lean model. Randomized tests cover the rest
    (the JSON translation, the Python glue, the engine): they generate
    random tables and batches with NULLs and duplicates, and after every
    batch compare the maintained view with a recompute, as the button does.
    `view.refresh(audit=True)` runs the same comparison in production and
    raises `AuditError` (from `sverify.errors`) before applying a wrong
    batch.

    ## Pipelines

    Real pipelines are layered: cleaned tables feed joined tables feed
    reports. In sverify the layers are transforms piped from the one
    below, so the code reads in the order the data flows:
    `orders.pipe(paid).pipe(doubled)` is the same node as
    `doubled(paid(orders))`, and the other inputs of a layer come by
    keyword. Without a `.write` in between, transforms fuse into one plan,
    maintained as one incremental view. `.write(sink)` stores a layer, and
    the layers above read the stored table as a versioned source through
    its change feed. An intermediate result is computed once and shared,
    and only changes flow through the layers. The base layer carries the
    contracts of chapter 4, and their guarantees hold in every state.
    """)
    return


@app.cell
def _(pa, StaticSource, arrow_table, sv):
    import tempfile
    from pathlib import Path

    from ibis import _
    from sverify.io import DeltaSink

    lake = Path(tempfile.mkdtemp())  # a local "lake"; any Delta URI works, with storage_options

    @sv.transform(
        requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, sv.unique("id")]},
        ensures=[_.amount >= 0, _.amount < 1_000_000_000, _.amount.notnull(), sv.unique("id")],
    )
    def paid(orders):
        return orders.filter(orders.amount.notnull())

    @sv.transform(
        requires={"t": [_.amount >= 0, _.amount < 1_000_000_000, _.amount.notnull()]},
        ensures=[_.doubled >= 0, _.doubled.notnull()],
    )
    def doubled(t):
        return t.select(t.id, t.customer, doubled=t.amount * 2)

    @sv.transform(requires={"base": [_.doubled.notnull()]}, ensures=[_.doubled.notnull()])
    def cities(base, customers):
        return base.join(customers, base.customer == customers.name).select("id", "city", "doubled")

    @sv.transform()
    def locations(base, customers):
        return base.left_join(customers, base.customer == customers.name).select("id", "city")

    feed = StaticSource(
        arrow_table(
            pa.schema({"id": pa.int64(), "customer": pa.string(), "amount": pa.int64()}),
            [(1, "ada", 30), (2, "bob", 5), (3, "cy", 0)],
        ),
        name="orders",
    )
    directory = StaticSource(
        arrow_table(
            pa.schema({"name": pa.string(), "city": pa.string()}),
            [("ada", "Paris"), ("cy", "Lima")],
        ),
        name="customers",
    )

    base = feed.pipe(paid).pipe(doubled).write(DeltaSink(str(lake / "base")))
    by_city = base.pipe(cities, customers=directory)
    by_location = base.pipe(locations, customers=directory)
    monday = sv.group(by_city, by_location)
    print(monday.refresh())
    return (
        base,
        by_city,
        by_location,
        cities,
        directory,
        feed,
        lake,
        monday,
    )


@app.cell(hide_code=True)
def _(mo):
    mo.mermaid(
        """
        graph BT
          O["orders"] --> B["base (Delta table)<br/>orders.pipe(paid).pipe(doubled), one fused plan"]
          B --> C["cities<br/>inner join customers"]
          B --> L["locations<br/>left join customers<br/>(recomputed)"]
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
        "`locations` read `base`'s Delta table.\n"
        "* A contracted transform piped from a stored node builds on what that node's "
        "plan proved, as in a direct composition. `cities` requires "
        "`_.doubled.notnull()` of `base`, which `doubled` guarantees, so Lean proves it "
        "once, when the node is built, and the data is never checked. A precondition "
        "`base` doesn't guarantee raises `CompositionError` right there.\n"
        "* `sv.group(by_city, by_location)` refreshes both reports against the same "
        "source versions. `base` is refreshed and written once for the two of them, "
        "upstream first. Its first refresh checked `paid`'s preconditions on all of "
        "`orders` (the `requires … (checked on data)` lines above).\n"
        "* `locations` is a left join, so each refresh recomputes and diffs it. "
        f"`status()` says so:\n\n```text\n{monday.status()}\n{base.status()}\n```"
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    We'll feed the pipeline. Each button changes `orders` and `customers`
    and refreshes both reports with `audit=True`, so every batch is also
    compared with a recompute before it is applied. The first button is
    valid. The other two each insert an order that breaks a precondition of
    `paid`.
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
def _(directory, dup, feed, good, monday, neg, presses, sv):
    from sverify.errors import PreconditionError

    _cities = ["Oslo", "Rome", "Lima", "Paris"]

    def _try(kind, changes):
        feed.apply(changes["orders"])
        if "customers" in changes:
            directory.apply(changes["customers"])
        try:
            presses["last"] = (kind, str(monday.refresh(audit=True)))
        except PreconditionError as e:
            presses["last"] = (kind, e)
            # The demo takes the bad order out of the feed again, so the
            # next batch can go through.
            feed.apply(sv.io.Changes(deletes=changes["orders"].inserts))

    while presses["good"] < good.value:
        _i = presses["good"]
        _try(
            "good",
            {
                "orders": sv.io.Changes(
                    inserts=[(10 + _i, "bob", 3 * _i), (20 + _i, f"new{_i}", 7)]
                ),
                "customers": sv.io.Changes(inserts=[(f"new{_i}", _cities[_i % 4])]),
            },
        )
        presses["good"] += 1
    while presses["dup"] < dup.value:
        _try("dup", {"orders": sv.io.Changes(inserts=[(1, "dee", 4)])})
        presses["dup"] += 1
    while presses["neg"] < neg.value:
        _try("neg", {"orders": sv.io.Changes(inserts=[(99, "eve", -5)])})
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
                    mo.md("The batch reached every layer, and the audit found no difference."),
                    kind="success",
                ),
                mo.md(f"`refresh(audit=True)` reports:\n\n```text\n{_last[1]}\n```"),
            ]
        )
    else:
        _msg = mo.callout(
            mo.md(
                f"`PreconditionError`: {_last[1]}. The refresh was refused; no layer "
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
    ### When the data breaks the contract

    A refused batch stops the report until someone fixes the feed. For a
    few bad rows among thousands, you may rather set them aside and let the
    rest through. With `on_violation="quarantine"` on the transform (or on
    the source), the refresh sets aside the rows that break a precondition,
    with the reason, and the node runs on the others
    ([#184](https://github.com/AlexanderNenninger/substrait-lean/issues/184)).
    A row is set aside when a row condition is not TRUE on it, or when
    another row shares its key: both rows of a repeated `id` go, so the rule
    needs no order between them. Every precondition holds on the rows that
    stay (`Catalog.kept_sound` in
    [`Quarantine.lean`](https://github.com/AlexanderNenninger/substrait-lean/blob/main/SubstraitLean/Quarantine.lean)),
    so `paid`'s proof holds as before. We feed a Delta table an order with a
    negative amount and one with an id that exists already:
    """)
    return


@app.cell
def _(lake, pa, sv):
    from deltalake import write_deltalake as _write
    from ibis import _
    from sverify.io import DeltaSink as _DeltaSink
    from sverify.io import DeltaSource

    _orders_uri = str(lake / "raw_orders")
    _write(
        _orders_uri,
        pa.table({"id": [1, 2, 3], "customer": ["ada", "bob", "cy"], "amount": [30, 5, 0]}),
        configuration={"delta.enableChangeDataFeed": "true"},
    )

    @sv.transform(
        requires={"orders": [_.amount >= 0, sv.unique("id")]},
        ensures=[_.amount >= 0, sv.unique("id")],
        on_violation="quarantine",
    )
    def clean(orders):
        return orders.select("id", "customer", "amount")

    clean_orders = DeltaSource(_orders_uri, name="orders").pipe(clean)
    clean_orders = clean_orders.write(_DeltaSink(str(lake / "clean")))
    clean_orders.refresh()
    _write(
        _orders_uri,
        pa.table({"id": [4, 5, 2], "customer": ["dee", "eve", "fay"], "amount": [12, -5, 9]}),
        mode="append",
    )
    flagged = clean_orders.refresh()
    print(flagged.summary())
    return clean_orders, flagged


@app.cell(hide_code=True)
def _(clean_orders, flagged, mo):
    mo.md(
        f"The refresh completed (`outcome` is `{flagged.outcome!r}`). Order 4 went "
        "through. Order 5 breaks `amount >= 0`. Order 2 is now on two rows, so both "
        "copies are set aside, the one `clean` held before included, until the feed "
        "says which is right. The rows sit in a Delta table next to the sink, "
        "`clean_quarantine`, with the reason and the source version, and "
        "`clean_orders.quarantined()` returns them. A scheduled job posts "
        "`flagged.alert()` to whoever is on call, for example as a GitHub issue:\n\n"
        f"{flagged.alert()}\n\n"
        f"`clean` now holds:\n\n```text\n{clean_orders.to_pandas().sort_values('id')}\n```"
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The fix comes from upstream: the feed deletes the wrong order 2 and
    corrects the amount of order 5. The next refresh releases the rows set
    aside, and they flow into `clean` and everything that reads it:
    """)
    return


@app.cell
def _(clean_orders, lake):
    from deltalake import DeltaTable as _DeltaTable

    _dt = _DeltaTable(str(lake / "raw_orders"))
    _dt.delete("id = 2 AND customer = 'fay'")
    _DeltaTable(str(lake / "raw_orders")).update(updates={"amount": "5"}, predicate="id = 5")
    fixed = clean_orders.refresh()
    print(fixed.summary())
    print(fixed.outcome, len(clean_orders.quarantined()))
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    `on_violation="hold"` holds the node at its versions instead: the
    refresh commits nothing for the batch, says why (`outcome` is
    `"held"`), and reads the batch again next time. The default,
    `"error"`, is what the buttons above do.

    A change to the schema breaks a contract in another way. Say the feed's
    owner lets `id` be NULL, and the next version has an order without one.
    `clean` was proved with `id` NOT NULL, so the refresh refuses, and the
    message names the column, the version and the contract:
    """)
    return


@app.cell
def _(lake, pa):
    import sverify as _sv
    from deltalake import write_deltalake as _write2
    from ibis import _ as _d
    from sverify.errors import SchemaError
    from sverify.io import DeltaSource as _DeltaSource

    _uri = str(lake / "events")
    _strict = pa.schema(
        [
            pa.field("id", pa.int64(), nullable=False),
            ("customer", pa.string()),
            ("amount", pa.int64()),
        ]
    )
    _write2(_uri, pa.Table.from_pylist([{"id": 1, "customer": "ada", "amount": 30}], _strict))

    @_sv.transform(requires={"orders": [_d.amount >= 0]}, ensures=[_d.id.notnull()])
    def keyed(orders):
        return orders.select("id", "amount")

    _node = _DeltaSource(_uri, name="orders").pipe(keyed)
    _node.refresh()
    _loose = pa.schema([("id", pa.int64()), ("customer", pa.string()), ("amount", pa.int64())])
    _write2(
        _uri,
        pa.Table.from_pylist(
            [
                {"id": 1, "customer": "ada", "amount": 30},
                {"id": None, "customer": "bob", "amount": 4},
            ],
            _loose,
        ),
        mode="overwrite",
        schema_mode="overwrite",
    )
    try:
        _node.refresh()
    except SchemaError as _e:
        print(f"SchemaError: {_e}")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### Why the guarantees survive every batch

    Whoever reads `base` relies on its guarantees on the hundredth batch as
    on the first. `paid`'s preconditions were checked on all of `orders`
    once, on the first refresh. After that only the batch is checked: row
    conditions (`amount >= 0`) on the inserted rows, and keys
    (`unique(id)`) among the inserted rows and against the keys of the
    rows the batch keeps. Theorem `Spec.update` in
    [`Compose.lean`](https://github.com/AlexanderNenninger/substrait-lean/blob/main/SubstraitLean/Compose.lean)
    says a table's contract survives a batch under exactly these checks,
    and `Triple.maintained` says a contracted view's guarantees then hold in
    the new state. So `base` satisfies `doubled ≥ 0` and is non-NULL after
    every batch without re-checking the whole table, and the Delta table
    it is written to records those guarantees with every version, for the
    layers that read it.

    The layering is `Rel.chain_sound` (DBSP's chain rule): when a view
    reads another view's stored result and gets that view's change as its
    change table, its own update plan is still correct. For a recomputed
    view, `ZSet.diff_correct` shows that `new − old` is a valid change to
    pass on. Each refresh brings the layers up to date upstream first and
    writes every stored node once per state. After a restart, building the
    same nodes and refreshing resumes each stored node from its table when
    the plan and the source versions match.

    ### Your own source and sink

    Say the customers don't live in the lake. The CRM team has an API that
    returns the customers who signed up after a given time, and finance
    wants the city report as a Parquet file on their share. A source you
    write is one method, `read(since)`, which returns the new rows and a
    cursor for the next read. A sink is one method, `write(change)`, which
    stores what a refresh hands it. Sverify numbers the reads as versions,
    works out what changed, checks the preconditions and decides when a
    state needs writing. We read the CRM with `from_query`, which keeps a
    high-water mark on a column, and write the report with a sink that
    keeps the contract next to the file, so a restarted job knows what it
    already wrote:
    """)
    return


@app.cell
def _(base, cities, lake, pa):
    import pyarrow.parquet as pq
    from sverify.io import Contract, Sink, from_query

    crm_signups = [
        {"name": "ada", "city": "Paris", "signed_up": 1},
        {"name": "cy", "city": "Lima", "signed_up": 2},
    ]

    def signed_up_after(since):
        """The CRM's API: customers who signed up after `since`."""
        return pa.Table.from_pylist(
            [c for c in crm_signups if since is None or c["signed_up"] > since]
        )

    class ParquetFile(Sink):
        """The report as a Parquet file, with its contract next to it."""

        def __init__(self, path):
            super().__init__(path.stem, location=str(path))
            self.path, self.record = path, path.with_suffix(".contract.json")

        def contract(self, version=None):
            if not self.record.exists():
                return None
            return Contract.from_json(self.record.read_text())

        def write(self, change):
            pq.write_table(change.table, self.path)
            self.record.write_text(change.contract.to_json())

    crm = from_query(signed_up_after, cursor_on="signed_up", name="crm")
    report = base.pipe(cities, customers=crm).write(ParquetFile(lake / "city_report.parquet"))
    print(report.refresh())

    crm_signups.append({"name": "bob", "city": "Oslo", "signed_up": 3})
    print(report.refresh())
    return crm_signups, report


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The first refresh read the CRM in full as version 1 and wrote the file.
    The second read only bob, as version 2, and the report says what that
    rests on: customers only arrive with a greater `signed_up`. That is
    the watermark job's assumption from chapter 1, and it can break. A
    sign-up the CRM records late, with an earlier time, falls below the
    cursor and is never read. We record one and audit, which reads the
    source again in full up to the cursor and compares it with what the
    batches built:
    """)
    return


@app.cell
def _(crm_signups, report):
    from sverify.errors import AuditError

    crm_signups.append({"name": "dee", "city": "Rome", "signed_up": 2})  # late
    print(report.refresh())  # nothing new above the cursor: dee is missed
    try:
        report.refresh(audit=True)
    except AuditError as e:
        print(f"AuditError: {e}")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The plain refresh saw nothing new, and the audit caught the row the
    cursor skipped and applied nothing. A source can promise no more than
    its reads do, so give it an `assumes=` that says what its batches rely
    on, and audit now and then. The rest of the toolkit, in `sverify.io`:

    * `from_frame(fn)` reads the whole table on every refresh and diffs it
      against the last read, so the change is exact and nothing is assumed.
      `from_files(path)` reads the files that are new in a directory.
      Subclass `Source` for anything else. A batch can be a whole table
      (`kind="snapshot"`) or rows added and removed (`kind="changes"`).
    * A sink's `write` gets a `SinkChange`: the rows added and removed
      since its last write, or the whole table on the first, with the
      contract to record. `contract()` reads that contract back, so each
      state is written once even across restarts; without it sverify
      remembers for the life of the process. `sink_from(fn)` hands the
      whole table to a function.
    * These sources have no metadata, so preconditions on them are checked
      on the rows, and they keep the table in memory. A restarted job reads
      them in full again and numbers its versions above the ones its sinks
      recorded. A table format with statistics and a change feed
      implements the full `VersionedSource` protocol, as Delta and Iceberg
      do.
    * `Storage` holds object store options, or a function that fetches
      fresh ones, shared by every table that needs them.

    ## Engines and SQL

    A proof is about the Lean model. Whether an engine computes what the
    model says is a separate question, and engines disagree about NULL join
    keys, NaN, integer overflow, the rounding of integer division and the
    order of ties. Plans come from one producer: the vendored Ibis
    producer, or sverify's lift of DuckDB's SQL (SQLGlot) for SQL strings.
    DuckDB (the default), Polars on its streaming engine and Spark 4.x run
    plans, each with a proved profile, and sverify writes DuckDB, Spark and
    Snowflake SQL; Snowflake's profile and running plans on it come before
    1.0. DataFusion is an optional engine outside the 1.x promise.
    [The engines](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/stability.md#engines) has the details. Lean's reference profile is the reference,
    one of the [profiles that refine the core](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/core-semantics.md#core-profiles-and-engines),
    and the tests use DuckDB as their default oracle. DuckDB and Polars are
    characterized fact by fact, each fact with its evidence
    ([the ledgers](https://alexandernenninger.github.io/substrait-lean/ledgers/)). DuckDB and Polars run Lean's
    written form of the plan (`sverify.engines.written_plan`), so what runs
    is what was checked, and their translators spell out the reference's
    semantics explicitly, whatever the engine's defaults.

    We'll line the engines up. Pick a query, and each engine runs the same
    checked plan (`sverify.engines.run(con, plan, engine)`) next to Lean's
    reference interpreter:
    """)
    return


@app.cell
def _(ibis, math, sv):
    from sverify.engines import ENGINES, run, substrait_json, written_plan

    T_SCHEMA = ibis.schema({"k": "string", "qty": "int64", "v": "float64"})
    U_SCHEMA = ibis.schema({"k": "string", "label": "string"})
    T_ROWS = [("a", 7, 1.5), ("b", -7, math.nan), (None, 2, 0.0), ("a", 2**63 - 1, None)]
    U_ROWS = [("a", "alpha"), (None, "nothing"), ("b", "beta")]

    con = sv.connect()
    con.create("t", T_SCHEMA, T_ROWS)
    con.create("u", U_SCHEMA, U_ROWS)
    return (
        ENGINES,
        T_ROWS,
        T_SCHEMA,
        U_ROWS,
        U_SCHEMA,
        con,
        run,
        substrait_json,
        written_plan,
    )


@app.cell(hide_code=True)
def _(con, display):
    display.side_by_side(
        display.table(con.rows("t"), ["k", "qty", "v"], title="t"),
        display.table(con.rows("u"), ["k", "label"], title="u"),
    )
    return


@app.cell(hide_code=True)
def _(mo):
    query = mo.ui.dropdown(
        {
            "join on a key that can be NULL": "select t.k, t.qty, u.label from t join u on t.k = u.k",
            "integer division (truncates)": "select qty, qty // 2 as half, qty % 2 as rest from t where qty < 100",
            "doubles: NaN": "select v, v > 0 as positive, v = 0.0 as is_zero from t",
            "qty + 1 (MAX overflows)": "select qty + 1 as next from t",
        },
        value="join on a key that can be NULL",
        label="query",
    )
    query
    return (query,)


@app.cell(hide_code=True)
def _(ENGINES, con, display, json, mo, query, run, substrait_json, written_plan):
    from sverify.testing import canonical, inline_tables, lean_rows

    _plan = substrait_json(con, query.value, semantics="duckdb")
    _written = written_plan(_plan)
    _cols = json.loads(_plan)["relations"][0]["root"]["names"]
    _panels, _results = [], {}
    for _engine in ENGINES:
        try:
            _t = run(con, _written, _engine)
            _results[_engine] = [tuple(r.values()) for r in _t.to_pylist()]
            _panels.append(display.arrow(_t, title=_engine))
        except Exception as _e:
            _panels.append(
                mo.vstack(
                    [
                        mo.md(_engine),
                        mo.callout(
                            mo.md(f"`{type(_e).__name__}`: {str(_e).splitlines()[0][:120]}"),
                            kind="danger",
                        ),
                    ]
                )
            )
    if " v" not in query.value and "+ 1" not in query.value:  # see the note below
        _data = {t: con.rows(t) for t in ("t", "u")}
        _lean = lean_rows(json.dumps(inline_tables(json.loads(_plan), _data)))
        _panels.insert(0, display.table(_lean, _cols, title="Lean's Rel.eval"))
    _same = len({repr(canonical(r)) for r in _results.values()}) == 1 and len(_results) == 3
    mo.vstack(
        [
            mo.md(f"```sql\n{query.value}\n```"),
            display.side_by_side(*_panels),
            mo.callout(
                mo.md("All three engines agree." if _same else "The engines disagree; see below."),
                kind="success" if _same else "warn",
            ),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    What to look for:

    * NULL join keys never match, because `NULL = NULL` is not TRUE. Each
      translator says so explicitly.
    * Integer division truncates toward zero, as in DuckDB's `//` and in
      Lean (`-7 // 2 = -3`). Polars' own `//` floors to `-4`, so its
      translator truncates.
    * NaN is one value, equal to itself and above every number, so
      `NaN > 0` is TRUE. The next section covers doubles.
    * `qty + 1` on the largest integer is where engines differ most:
      DataFusion (optional, outside the 1.x promise) wraps around to the
      smallest integer, while the Polars and DuckDB translators raise, as
      the reference does. An integer that
      leaves its declared width is an error, and `verify` reports it
      beforehand.

    Lean's column is missing for the last two queries. The model stores a
    double as a very large integer code (`core/Sverify/Core/Float.lean`), so
    the checker's printer can't tell a double from an integer beyond 64
    bits. The test suite compares doubles through the engines.

    ### Choosing the engine for a node

    A node doesn't fix its engine. The plan is the same everywhere, and
    `node.refresh(engine="polars")` (or `"spark"`, a Spark session) picks where it runs; DuckDB in memory is the default. A node
    keeps its state between refreshes, so the next refresh may use another
    engine. Contracts checked on data take `engine=` too:
    `@sv.transform(ensures=[...], on_unproved="check", check_engine="duckdb")`.
    We refresh a fresh node of the NULL-key join on each engine:
    """)
    return


@app.cell
def _(ENGINES, StaticSource, T_ROWS, T_SCHEMA, U_ROWS, U_SCHEMA, pa, sv):
    def _source(schema, rows, name):
        _arrow = schema.to_pyarrow()
        return StaticSource(
            pa.Table.from_pylist([dict(zip(_arrow.names, r)) for r in rows], schema=_arrow),
            name=name,
        )

    _t, _u = _source(T_SCHEMA, T_ROWS, "t"), _source(U_SCHEMA, U_ROWS, "u")

    @sv.transform()
    def labelled(t, u):
        return t.join(u, t.k == u.k).select(t.k, t.qty, u.label)

    by_engine = {}
    for _engine in ENGINES:
        _node = _t.pipe(labelled, u=_u)
        _node.refresh(engine=_engine)
        by_engine[_engine] = sorted(tuple(r.values()) for r in _node.to_arrow().to_pylist())
    by_engine
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Every engine returns the same rows, and the NULL key matches nothing.

    ### Splitting a plan across machines

    When a table outgrows one machine, its rows live in pieces, and the plan
    has to run piece by piece. `sverify.engines.run_sharded` asks the
    checker how the plan splits: what each shard computes, and how the
    parts combine into the plan's result on all the rows
    (`Rel.shardSplit_sound`). It runs each shard on Polars and refuses a
    plan whose result would depend on the split. We'll total each meter's
    readings, kept in two regions:
    """)
    return


@app.cell
def _(pa, substrait_json, sv):
    from sverify.engines import run_sharded

    def _readings(rows):
        return pa.table(
            {
                "meter": pa.array([m for m, _, _ in rows], pa.int64()),
                "wh": pa.array([w for _, w, _ in rows], pa.int64()),
                "kwh": pa.array([k for _, _, k in rows], pa.float64()),
            }
        )

    regions = [
        {"readings": _readings([(1, 120, 0.12), (2, 300, 0.3), (1, 80, 0.08)])},
        {"readings": _readings([(2, 50, 0.05), (3, 10, 0.01)])},
    ]
    _con = sv.connect()
    _con.create("readings", regions[0]["readings"].schema)
    wh_plan = substrait_json(_con, "SELECT meter, SUM(wh) AS wh FROM readings GROUP BY meter")
    kwh_plan = substrait_json(_con, "SELECT meter, SUM(kwh) AS kwh FROM readings GROUP BY meter")
    _wh = run_sharded(wh_plan, regions, sharded=["readings"])
    sorted(_wh.to_pylist(), key=lambda r: r["meter"])
    return kwh_plan, regions, run_sharded


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    An integer sum splits exactly: each region sums its meters, and the
    parts add up. A sum of doubles doesn't, since each region rounds its
    partial sum, and the rounding depends on which rows land where. The
    plan is refused, and the refusal names the way through:
    """)
    return


@app.cell
def _(kwh_plan, regions, run_sharded):
    try:
        run_sharded(kwh_plan, regions, sharded=["readings"])
    except ValueError as _e:
        print(f"{type(_e).__name__}: {_e}")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    With `reproducible=sv.equivalent(floats="plan")` we accept doubles
    within the bound the proof gives for this split
    (`StdModel.sharded_near`), and `tolerance=True` reports it per row:
    """)
    return


@app.cell
def _(kwh_plan, regions, run_sharded, sv):
    _kwh = run_sharded(
        kwh_plan,
        regions,
        sharded=["readings"],
        reproducible=sv.equivalent(floats="plan"),
        tolerance=True,
    )
    assert _kwh.rows_exact
    {
        "kwh": _kwh.table.sort_by("meter").to_pylist(),
        "within": _kwh.tolerance["kwh"],
    }
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Each meter's total is within a few units of 10⁻¹⁶ of the sum on one
    machine, and the bound comes with the result.

    ### Routes: how a proof reaches an engine

    A proof is about the plan under one semantics, the reference by default.
    `report.run(con, engine, route="auto")` and
    `node.refresh(engine=..., route="auto")` choose how it reaches the
    engine, and refuse the plan with the reason where nothing does (D13 in
    [core-semantics.md](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/core-semantics.md#d13-choosing-the-route)).
    The route names the plan's class on the engine: `exact` (every result
    the engine gives, the reference allows), `observed` (equal under an
    observation the postcondition states, a float tolerance included),
    `shim` (after a proved translation) or `refused`. Before the plan runs, its preconditions
    are checked on the data. We take the join to Polars:
    """)
    return


@app.cell
def _(con, mo, sv):
    _t, _u = con.table("t"), con.table("u")
    _routed = sv.verify(_t.join(_u, _t.k == _u.k).select(_t.k, _t.qty, _u.label))
    _routed.run(con, "polars", route="auto")
    mo.md(f"Route on Polars: {_routed.routes['polars']}")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    A stored node also needs a rerun to reproduce its result, since its sink
    commits each epoch once. The sink states what that means: exact bits
    (`reproducible=sv.equivalent()`), or doubles within a tolerance,
    `DeltaSink(uri, reproducible=sv.equivalent(floats=sv.within(abs=1e-6)))`,
    for a `SUM` of doubles, which Polars's streaming engine may add in
    another order each run. A refresh whose route cannot meet that is
    refused. The
    [examples](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/examples.md) show both, step by step.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### SQL for DuckDB, Snowflake and Spark

    When the data lives in a warehouse, the plan goes to the warehouse.
    `sverify.engines.to_sql` writes a checked plan, or one of Lean's update
    plans, as SQL whose result is `Rel.eval` of the plan. Columns are
    positional (`c0`, `c1`, …), filters keep only TRUE rows (`IS TRUE`),
    integers are checked at their declared width and every `ORDER BY` says where
    NULLs go. Each engine's differences go through a `Dialect`:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    dialect = mo.ui.radio(
        ["duckdb", "snowflake", "spark"], value="duckdb", label="dialect", inline=True
    )
    sql_query = mo.ui.text_area(
        value="select k, qty * 2 as doubled from t where qty > 0",
        label="query over t(k, qty, v)",
        full_width=True,
        rows=2,
    )
    mo.vstack([sql_query, dialect])
    return dialect, sql_query


@app.cell(hide_code=True)
def _(con, dialect, json, mo, sql_query, substrait_json):
    import sqlglot
    from sverify.engines import DUCKDB, SNOWFLAKE, SPARK, UnsupportedError, to_sql

    try:
        _plan = json.loads(substrait_json(con, sql_query.value, semantics="duckdb"))
        _dialects = {"duckdb": DUCKDB, "snowflake": SNOWFLAKE, "spark": SPARK}
        _sql = to_sql(_plan, _dialects[dialect.value])
        _pretty = sqlglot.transpile(_sql, read=dialect.value, pretty=True)[0]
        _out = mo.md(f"```sql\n{_pretty}\n```")
    except UnsupportedError as _e:
        _out = mo.callout(mo.md(f"`UnsupportedError` in {dialect.value}: {_e}"), kind="warn")
    except Exception as _e:
        _out = mo.callout(mo.md(f"`{_e}`"), kind="danger")
    _out
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Try `select k, row_number() over (partition by k order by qty) as rn from t`
    in each dialect. DuckDB gets an ordinal column, so ties break the way
    Lean's stable sort breaks them. Snowflake and Spark refuse, because
    their tables have no row order. When a contract report says
    `deterministic` (chapter 4), `deterministic=True` promises there are no ties
    and the SQL is written.

    Snowflake: integers are `NUMBER(38,0)` checked against the 64-bit
    range, timestamps are `TIMESTAMP_NTZ(6)`, every identifier is quoted,
    and interval-valued result columns are refused because Snowflake has no
    interval type.

    Spark and Databricks: the dialect (`sverify.engines.SPARK`) targets
    Spark 4 and is also what `node.refresh(engine="spark")` runs. It
    assumes the session settings of `sverify.engines.SPARK_CONF`, above all
    `spark.sql.ansi.enabled`: without ANSI mode an overflow wraps around
    and a bad cast gives NULL. Spark answers several questions its own way,
    and the SQL spells out or refuses each:

    * `/` of integers is a double, so division is `div`. `/` of doubles
      raises on a zero divisor, as the reference does; a plan that asks for
      IEEE gets ±inf or NaN from a `CASE`.
    * `CAST(9.3e18 AS BIGINT)` saturates, and `FLOOR` and `CEIL` return
      integers. Each is range-checked or repaired.
    * `SUM` of `BIGINT` raises on an overflowing partial sum even when the
      total fits, so it adds `DECIMAL(38,0)`.
    * `TIMESTAMP` is the session time zone's, and so is what `date_trunc`
      returns, so the SQL stays in `TIMESTAMP_NTZ`.
    * `POWER` of doubles is Java's `Math.pow` (within 1 ulp of C's) and is
      refused, as are sorts and windows over a table without
      `deterministic=True`.

    Spark runs locally, unlike Snowflake. The tests run every coverage case
    and every query of the Snowflake suite on a local Spark session
    (Java 17 or 21) and compare them with `Rel.eval`. The Lean evaluator is
    the specification: the suite runs every fixture and every update plan
    on Polars and DuckDB, and on the optional DataFusion, with random
    tables, and compares them
    with each other and with `Rel.eval`, row for row in Lean's order where
    order matters. The Snowflake SQL is parsed and run on fakesnow. The
    [engine profiles](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/engine-profiles.md)
    list where each engine departs from the reference.

    ## Doubles, time and text

    Say one of your sensors sends NaN, or a timestamp lands at the edge of
    the calendar. Floating-point measurements, timestamps and strings each
    have traps, and the Lean model pins them down bit for bit where it
    matters, because a proof about the wrong semantics proves nothing.

    ### Doubles: NaN, infinities and one zero

    In IEEE 754 comparisons and in Python, NaN equals nothing, itself
    included. SQL engines (PostgreSQL, DuckDB, Spark, Snowflake) order
    doubles differently, and so does sverify's reference profile:

    > −∞ < … < 0.0 < … < +∞ < NaN

    There is one NaN, equal to itself and larger than every number, and one
    zero: −0.0 is 0.0, so `-0.0 >= 0` holds and −0.0 never shows in a
    result. Lean's core keeps both zeros and signed NaNs, and the reference
    profile reads them this way
    ([core, profiles and engines](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/core-semantics.md#core-profiles-and-engines)).
    DataFusion's own order, `f64::total_cmp`, splits both, so
    sverify stores DataFusion's tables the reference's way
    ([`docs/how-it-works.md`](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/how-it-works.md#doubles-under-the-reference-profile)).
    Here is a table with both zeros and NaN:
    """)
    return


@app.cell
def _(con, ibis, math):
    con.create(
        "m",
        ibis.schema({"v": "float64"}),
        [(1.5,), (math.nan,), (-1.0,), (0.0,), (-0.0,), (math.inf,), (-9999.0,), (None,)],
    )
    return


@app.cell(hide_code=True)
def _(con, display):
    from sverify.testing import duckdb_ibis, duckdb_sql

    display.arrow(
        duckdb_sql(
            con,
            "select v, v > 0 as positive, v = 'NaN'::double as equals_nan,"
            " v < 'Infinity'::double as below_inf from m order by v",
        ),
        title="the table's doubles, as the model has them",
    )
    return duckdb_ibis, duckdb_sql


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Two consequences. `v > 0` keeps NaN rows, so a filter meant as
    "positive readings" lets glitches through, and only an upper bound
    (`v < 1e9`, say) removes NaN. And the table was given both zeros and
    holds one: `DISTINCT` keeps a single zero and `-1 * 0.0` is `0.0`, on
    every engine. Lean models doubles exactly, as integer codes in the same
    order, so the proofs know all of this. We build a filter and see
    whether "no NaN" follows:
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
    Comparisons with constants are exact, sentinels like `-9999.0` and the
    boundary between `v > 0.5` and `v >= 0.5` included. Arithmetic on
    doubles (`v * 2.5`) rounds, and the checker bounds `+`, `-`, `*` and `/`
    from their inputs' bounds with a proved rounding error
    ([float bounds](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/float-bounds.md#one-operations-bounds-and-overflow-582)).
    The reference raises where an operation on finite doubles overflows to
    ±∞, so where no bound keeps `v * 2.5` finite, the report assumes it
    stays finite and the run checks it on the data first: a ±∞ in a result came from the
    data ([#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575)). For the same reason `power(-inf, 0.5)`
    and a `MEDIAN` between −∞ and +∞ raise, where engines disagree. `FLOOR`, `CEIL`, `ROUND` and the cast to an integer are
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
    ### Timestamps and intervals

    Timestamps are microseconds since 1970 (UTC) in the model, and
    intervals are durations. Comparisons with literals, `ts + interval`,
    `ts1 - ts0` and joins on time are tracked like integers. The calendar
    functions are computed exactly on the Gregorian calendar
    ([`Time.lean`](https://github.com/AlexanderNenninger/substrait-lean/blob/main/core/Sverify/Core/Time.lean)),
    and Lean proves they grow with the timestamp, so a range of timestamps
    gives a range of years and of truncated months. Pick a time window and
    see what Lean derives:
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
    Within one calendar year, `year` is that exact integer. Truncations
    stay inside the window's range, rounded down, and `hour` is in
    `[0, 23]`, a proved range that doesn't grow with the timestamp. Without
    the filter, truncating to a month may fail near the ends of the
    timestamp range, so the plan needs `ts` between 1678 and 2262, the range
    of nanosecond timestamps. Sverify works it out and asks you to declare it
    (chapter 4 shows how inferred bounds work):
    """)
    return


@app.cell
def _(events, sv):
    sv.verify(events.select(month_start=events.ts.truncate("M")))
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### Text

    Strings are sequences of Unicode characters in the model. `substring`,
    `strpos`, `character_length`, `trim`, `||` and `LIKE` are computed
    exactly, and the test suite checks them against DuckDB on random
    strings. Here is Lean's `Rel.eval` next to DuckDB, running Ibis's own
    SQL, on some awkward words:
    """)
    return


@app.cell
def _(con, display, duckdb_ibis, ibis, json):
    from sverify.ibis_substrait import to_substrait_json
    from sverify.testing import inline_tables as _inline_tables
    from sverify.testing import lean_rows as _lean_rows

    con.create("w", ibis.schema({"word": "string"}), [("Grüße",), ("naïve ",), ("a%b",), (None,)])
    _w = con.table("w")
    _words = _w.select(
        "word",
        middle=_w.word.substr(1, 3),
        len=_w.word.length(),
        literal_percent=_w.word.like("a\\%b"),
        trimmed=_w.word.strip(),
        eszett=_w.word.find("ß"),
    )
    _plan = json.loads(to_substrait_json(_words))
    _cols = _plan["relations"][0]["root"]["names"]
    _lean = _lean_rows(json.dumps(_inline_tables(_plan, {"w": con.rows("w")})))
    display.side_by_side(
        display.table(_lean, _cols, title="Lean"),
        display.arrow(duckdb_ibis(con, _words), title="DuckDB"),
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    `UPPER`, `LOWER` and regular expressions are black boxes: Lean knows
    they return a string (or a boolean), and no proof depends on which one,
    because Unicode case mapping and regex engines are large and
    engine-specific. A regular expression is a possible runtime error
    unless Lean can see that it compiles. Patterns in a conservative subset
    of Rust's syntax are accepted, and anything fancier is reported. A
    back-reference like `\1` isn't supported by DataFusion's engine at
    all:
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
    Contracts don't track string contents yet: `startswith('acc')` in a
    filter doesn't let Lean prove `startswith('ac')` afterwards. Lengths,
    NULLs and errors are tracked.

    You can now keep a join up to date from its changes, stack contracted
    transforms into layers that pass only their changes along, and rely on
    their guarantees in every state while only each batch is checked. You
    can refresh a node on DuckDB, Polars or Spark, hand a plan
    to Snowflake as SQL, and tell where an engine could depart from the
    model. That is the end of the tour. The
    [guide](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/guide.md)
    covers every feature in more detail, and
    [how it works](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/how-it-works.md)
    goes under the hood: the checker, the producers and engines, and what
    is proved and what is trusted.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 4. [Contracts](?file=04_contracts.py)
    """)
    return


if __name__ == "__main__":
    app.run()

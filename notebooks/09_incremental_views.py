# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "ibis-framework==12.0.0",
#     "marimo",
#     "pyarrow==26.0.0",
#     "sverify==0.3.0",
# ]
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="medium", app_title="9. Incremental views")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 8. [Composing contracts](?file=08_composition.py) · [Contents](?file=00_start_here.py) · 10. [Pipelines](?file=10_pipelines.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 9. Incremental views

    Say your dashboard table is a join over a few million orders, and a
    hundred orders change every hour. Recomputing the whole join each time
    is slow; hand-written incremental logic ("only process rows where
    `updated_at` is newer than…") is fast, but tends to go wrong silently:
    deletes are missed, late rows are skipped, a join gets a new match.
    Nobody notices until the analyst reading the dashboard finds totals
    that no longer add up.

    *Incremental view maintenance* computes only the **change** to the
    result from the **changes** to the inputs. A source piped into a
    transform is a *node*, and `node.refresh()` keeps it up to date with
    update rules proved correct in Lean, on DuckDB, Polars, DataFusion or
    Spark (chapter 11). We'll use it first, see what it recomputes
    instead, and then look at how it works.

    ## Keeping a join up to date

    You write the query once, as an Ibis transform. We pipe one source into
    it and pass the other by keyword, which builds a node; `refresh()` computes its result once, and from then on
    keeps it up to date from the inserts and deletes alone. Here the
    sources are in-memory tables (`StaticSource`, from `sverify.io`); Delta
    and Iceberg tables work the same way (chapter 1 reads a Delta table):
    """)
    return


@app.cell
def _():
    import pyarrow as pa
    import sverify as sv
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
    return customers, delta_plans, orders, orders_with_city, sv, view


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    `orders.apply(sv.Changes(inserts=[...], deletes=[...]))` changes a
    source and gives it a new version; the next `view.refresh()` gets
    exactly that change and updates the view from it. To check, we build
    the same node again and refresh it: a node that has never been
    refreshed computes its result from scratch. We'll throw some changes at
    it: press the button to change both tables at once, at random.
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
def _(apply_batch, customers, delta_plans, display, mo, orders, orders_with_city, sv, view):
    import random as _random

    def _rows(table):
        return sorted((tuple(r.values()) for r in table.to_pylist()), key=repr)

    def _batch(rng, source, make_row):
        current = _rows(source.table)
        deletes = rng.sample(current, k=min(len(current), rng.randint(0, 2)))
        changes = sv.Changes(
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
                    f"After {apply_batch.value} batch(es): the maintained view "
                    + ("**equals** full recomputation ✓" if _equal else "**differs** ✗")
                    + f". Each batch runs {len(delta_plans(view.plan))} Lean-generated"
                    " update plans on DuckDB."
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
    ## What can be maintained

    A view that is quietly wrong is worse than no view, so the rule is
    strict. Filters, computed columns, inner joins (self-joins too), cross
    joins, `UNION ALL` and `ORDER BY` are maintained from their changes.
    Everything else is **recomputed and diffed** on every refresh instead
    of being maintained wrongly: left, semi and anti joins (a left join's
    NULL-padded rows must be *retracted* when a match turns up later),
    `DISTINCT`, `LIMIT` (it depends on row order), windows, and aggregates
    (contracts work on them, but their update rules aren't proved yet).
    The result is just as right, but it costs a full run per refresh, and
    `node.status()` tells you which kind of node you have. Pick one:
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
    return KINDS, kind


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
    result, still flows to the nodes that read it; that is how chapters 2
    and 3 maintain a window and an aggregate. The reason `status()` gives
    is a short, generic one; the list above is the full one.

    Nodes are built from Ibis transforms: a view written as a SQL string
    has no public counterpart yet. And the view is a table like any other:
    `view.table` is an Ibis table to query further, and `view.to_arrow()`,
    `to_polars()` and `to_pandas()` hand you its rows.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## How it works: rows with weights

    So how does the view know what changed? The trick that makes it
    tractable is to give every row a **weight**:

    * `+1`: this row was inserted,
    * `−1`: this row was deleted,
    * an update is a delete plus an insert.

    A table with weights is called a *Z-set*. Adding a batch of changes
    means putting the weighted rows together and summing the weights per
    row. Here's a small mirror of `SubstraitLean/Incremental.lean`, and a
    query over it:
    """)
    return


@app.cell
def _():
    def is_true(v):
        return v is True

    def lt(a, b):
        return None if a is None or b is None else a < b

    def eq(a, b):
        return None if a is None or b is None else a == b

    def mul(a, b):
        return None if a is None or b is None else a * b

    # Z-sets: lists of (row, weight).
    def z_lift(rows):
        return [(r, 1) for r in rows]

    def z_filter(z, cond):
        return [(r, w) for r, w in z if is_true(cond(r))]

    def z_map(z, f):
        return [(f(r), w) for r, w in z]

    def z_cross(a, b):
        return [(x + y, w * v) for x, w in a for y, v in b]

    def consolidate(z):
        """Sum the weights of equal rows; drop rows whose weight is 0."""
        totals = {}
        for r, w in z:
            totals[tuple(r)] = totals.get(tuple(r), 0) + w
        return sorted(((list(r), w) for r, w in totals.items() if w != 0), key=repr)

    def z_query(z):
        """SELECT id, amount * 2 AS doubled FROM orders WHERE amount > 10, on weighted rows."""
        kept = z_filter(z, lambda r: lt(10, r[2]))
        return z_map(kept, lambda r: [r[0], mul(r[2], 2)])

    order_rows = [[1, "ada", 30], [2, "bob", 5], [3, "ada", None]]
    return consolidate, eq, order_rows, z_cross, z_filter, z_lift, z_query


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Pick some changes to `orders`:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    changes = [
        mo.ui.checkbox(value=True, label="Delete order 1 (ada, 30)"),
        mo.ui.checkbox(value=True, label="Insert order 4 (cy, 50)"),
        mo.ui.checkbox(value=True, label="Update order 2: amount 5 → 20"),
        mo.ui.checkbox(value=False, label="Insert order 5 (dee, amount NULL)"),
    ]
    mo.vstack(changes, gap=0.25)
    return (changes,)


@app.cell(hide_code=True)
def _(changes):
    _all_changes = [
        [([1, "ada", 30], -1)],
        [([4, "cy", 50], +1)],
        [([2, "bob", 5], -1), ([2, "bob", 20], +1)],
        [([5, "dee", None], +1)],
    ]
    delta_orders = [c for box, cs in zip(changes, _all_changes) if box.value for c in cs]
    return (delta_orders,)


@app.cell(hide_code=True)
def _(consolidate, delta_orders, display, mo, order_rows, z_lift, z_query):
    _old = consolidate(z_query(z_lift(order_rows)))
    _delta_out = consolidate(z_query(delta_orders))
    _incremental = consolidate(z_query(z_lift(order_rows)) + z_query(delta_orders))
    _recomputed = consolidate(z_query(z_lift(order_rows) + delta_orders))
    mo.vstack(
        [
            display.side_by_side(
                display.zset(delta_orders, ["id", "customer", "amount"], "Δ orders (the changes)"),
                display.zset(
                    _delta_out, ["id", "doubled"], "query(Δ orders): the change to the result"
                ),
            ),
            display.side_by_side(
                display.zset(_old, ["id", "doubled"], "old result"),
                display.zset(_incremental, ["id", "doubled"], "old + change (incremental)"),
                display.zset(_recomputed, ["id", "doubled"], "recomputed from scratch"),
            ),
            display.verdict(
                _incremental == _recomputed,
                "Incremental result **equals** full recomputation ✓",
                "Mismatch ✗",
            ),
        ],
        gap=1.5,
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    For this query the rule is simple: **run the same query on only the
    changes**, then add the result to the old one. That works because
    filter and project treat each row independently (they are *linear*).
    In Lean that is theorem `Rel.zeval_add`:

    ```lean
    theorem Rel.zeval_add : r.Incremental →
        (r.zeval (cat + Δ)).Perm (r.zeval cat ++ r.zdelta cat Δ)
    ```

    Read: *for every plan in the supported fragment, evaluating on the
    updated database gives the old result plus the delta (in some order:
    `Perm` means "same rows, possibly reordered").*

    ## Joins are trickier

    A join pairs rows from two tables. If **both** tables change, the new
    result has four kinds of pairs:

    | | old customers `B` | new customers `ΔB` |
    |:---|:---|:---|
    | **old orders `A`** | `A × B`: already in the old result | `A × ΔB`: new |
    | **new orders `ΔA`** | `ΔA × B`: new | `ΔA × ΔB`: new, and easy to forget |

    So the change to a join is `ΔA × B + ΔA × ΔB + A × ΔB`. Forgetting the
    bottom-right cell is a classic bug in hand-written incremental
    pipelines. Toggle it off to see what goes wrong:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    include_corner = mo.ui.switch(value=True, label="include the ΔA × ΔB term")
    include_corner
    return (include_corner,)


@app.cell(hide_code=True)
def _(
    consolidate,
    delta_orders,
    display,
    eq,
    include_corner,
    mo,
    order_rows,
    z_cross,
    z_filter,
    z_lift,
):
    _customers = z_lift([["ada", "Paris"], ["bob", "Oslo"]])
    _delta_customers = [(["cy", "Lima"], +1), (["bob", "Oslo"], -1)]

    def _join(a, b):
        # orders.customer ($1) = customers.name ($3)
        return z_filter(z_cross(a, b), lambda r: eq(r[1], r[3]))

    _A, _dA = z_lift(order_rows), delta_orders
    _B, _dB = _customers, _delta_customers
    _delta = _join(_dA, _B) + _join(_A, _dB) + (_join(_dA, _dB) if include_corner.value else [])
    _incremental = consolidate(_join(_A, _B) + _delta)
    _recomputed = consolidate(_join(_A + _dA, _B + _dB))
    _cols = ["id", "customer", "amount", "name", "city"]
    mo.vstack(
        [
            mo.md(
                "Customer changes: insert **cy (Lima)**, delete **bob (Oslo)**. Order changes: as selected above."
            ),
            display.side_by_side(
                display.zset(_incremental, _cols, "incremental (old join + delta)"),
                display.zset(_recomputed, _cols, "recomputed from scratch"),
            ),
            display.verdict(
                _incremental == _recomputed,
                "Equal ✓",
                "**Different ✗**: rows are missing or have the wrong weight.",
            ),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    With the default changes, turning the switch off breaks the result in
    two ways:

    * the pair *order 4 + customer `cy`* is missing. Both are new, so only
      the corner term produces it;
    * phantom `bob` rows appear, one with weight **−1**: a row that "exists
      minus one times". The updated order 2 was paired with the *old* `bob`,
      and only the corner term cancels that pairing with `bob`'s deletion.

    Lean proves the full rule once and for all, and goes one step further:
    `Rel.delta` *generates* the update plan automatically, as an ordinary
    plan that reads the old tables and the change tables, and
    `Rel.delta_correct` proves the generated plan computes exactly the
    change. Since the update plan is an ordinary plan, any engine can run
    it.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## What runs on each batch

    The three update plans are exactly the three new cells of the join
    table above, as Lean wrote them; `sverify.engines.delta_plans(view.plan)`
    gives them to you. `orders$delta` and
    `customers$delta` are the change tables, with a trailing `__weight`
    column; old tables get weight 1 (`Project +[1]`), and the join
    multiplies weights (`$3 * $6`):
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
        [mo.md(f"```text\n{_tree(p)}\n```") for p in delta_plans(view.plan)],
        justify="start",
        wrap=True,
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Step by step:

    1. The transform becomes a Substrait plan (sverify's Ibis producer);
       `view.plan` is that plan as Lean checked and wrote it.
    2. `substrait-check --delta` builds the update plan (`Rel.delta`),
       splits it into pieces without `UNION ALL` (`Rel.terms`), and encodes
       each row's weight as the `__weight` column (`Rel.weighted`). Each step
       has a theorem saying it computes exactly the change to the result;
       `Rel.weighted_eval` covers running it on an ordinary engine.
    3. On each refresh, `sverify` registers the change tables, runs the
       plans, sums the weights per row, and merges the result into the
       view's state.

    A batch is computed completely before anything is replaced, so if
    anything fails, nothing changes. A change that can't happen at all,
    such as deleting a row that doesn't exist, doesn't even get that far:
    the source refuses it, and neither `orders` nor the view moves.
    """)
    return


@app.cell
def _(mo, orders, sv, view):
    _before = orders.version, view.versions
    try:
        orders.apply(sv.Changes(inserts=[(7, "ada", 70)], deletes=[(99, "nobody", 1)]))
    except ValueError as _e:
        _err = _e
    mo.callout(
        mo.md(
            f"**ValueError**: {_err}. `orders` is still at version {orders.version}, "
            f"and the view still reflects {view.versions}: "
            f"{(orders.version, view.versions) == _before}."
        ),
        kind="warn",
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### How do I know it's right?

    Before you point a dashboard at it, you'll want more than a demo. The
    theorems cover the Lean model. The rest (the JSON translation, the
    Python glue, the engine itself) is covered by randomized tests: they
    generate random tables and random batches, with NULLs and duplicates,
    and after every batch compare the maintained view with a full
    recompute, as the button above does. In production you can ask for
    the same check on every batch: `view.refresh(audit=True)` compares the
    batch with recomputation before applying it, and raises `AuditError`
    (from `sverify.errors`) instead of applying a wrong one.

    You can now keep a join up to date from its changes alone, with update
    rules proved in Lean, and you know which queries are recomputed rather
    than maintained wrongly. Next up, [Pipelines](?file=10_pipelines.py)
    stacks transforms into layers, stores the ones others read, so each
    change flows through every layer, and brings back the contracts of
    chapter 8.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 8. [Composing contracts](?file=08_composition.py) · [Contents](?file=00_start_here.py) · 10. [Pipelines](?file=10_pipelines.py) →
    """)
    return


if __name__ == "__main__":
    app.run()

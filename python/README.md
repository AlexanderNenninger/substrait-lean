# sverify

**Data pipelines with proofs: incremental views and pre/postconditions on
[DataFusion](https://datafusion.apache.org) or [Polars](https://pola.rs), checked in
[Lean](https://lean-lang.org).**

You write a query once, in [Ibis](https://ibis-project.org) or SQL. `sverify`
then does two things with it:

* **Incremental views.** It keeps the query's result up to date from inserts
  and deletes alone, without recomputing it. The update logic is a delta plan
  that is *proven* to give the same result as a full recompute.
* **Contracts.** You state what you assume about the inputs (`requires`) and
  what the output guarantees (`ensures`). The postconditions are *proved*
  before your pipeline runs, not sampled in tests.

The proofs live in the [substrait-lean](https://github.com/AlexanderNenninger/substrait-lean)
repository. The wheel ships the checker as a small native binary, so you need
neither Lean nor any other toolchain to use it.

```bash
pip install sverify          # or: uv add sverify
```

Wheels are available for Linux (x86_64, aarch64) and macOS (arm64, x86_64),
on Python 3.12 and later.

## Try it in the browser

Two [marimo](https://marimo.io) notebooks walk through the ideas with live
examples. No prior knowledge of formal verification is needed.

* [A gentle introduction](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/main/notebooks/intro.py):
  plans, proofs, SQL's NULL pitfalls and incremental updates, explained from scratch.
* [A verified fitness pipeline](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/main/notebooks/fitness.py):
  heart-rate samples joined with workouts, a contract with proved and refused
  postconditions, and a view you can stream samples into.

## Incremental views

```python
import ibis
import sverify as sv

con = sv.connect()  # an Ibis DataFusion backend
sv.create_table(
    con,
    "orders",
    ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
    [(1, "ada", 30), (2, "bob", 5)],
)
sv.create_table(
    con, "customers", ibis.schema({"name": "string", "city": "string"}), [("ada", "Paris")]
)

orders, customers = con.table("orders"), con.table("customers")
big_orders = (
    orders.filter(orders.amount > 10)
    .join(customers, orders.customer == customers.name)
    .select(orders.id, customers.city, orders.amount)
)

view = sv.IncrementalView(con, big_orders, "big_orders")
view.rows()  # [(1, 'Paris', 30)]

# Both tables change at once: order 1 leaves, order 3 arrives,
# and bob's new customer row makes his order match the join.
view.apply(
    {
        "orders": sv.Changes(inserts=[(3, "bob", 50)], deletes=[(1, "ada", 30)]),
        "customers": sv.Changes(inserts=[("bob", "Rome")]),
    }
)
view.rows()  # [(3, 'Rome', 50)]
assert view.rows() == view.recompute()
```

* An update is a delete plus an insert.
* `apply` also updates the base tables, and it is all or nothing: a failing
  batch, such as one that deletes a row that doesn't exist, changes nothing.
* The view is registered as a table, so you can query it with `con.table("big_orders")`.
* Plain SQL works too: `sv.IncrementalView(con, "select ... from ...", "name")`.
* `engine="polars"` runs the view's plans on Polars instead of DataFusion:
  exactly the plans Lean checked, translated by `sverify` rather than recompiled.

**Supported:** filters, computed columns, inner joins (including self-joins and
non-equi joins), cross joins and `UNION ALL`. Anything else is refused up
front, rather than maintained incorrectly:

```python
sv.IncrementalView(con, orders.limit(5), "top5")
# NotIncremental: not incrementally maintainable (left join, fetch or window)
```

Aggregates (`GROUP BY` with `SUM` or `COUNT`) are not supported yet.

## Contracts

```python
from ibis import _


@sv.transform(
    requires={"orders": [_.amount >= 0, _.id.notnull()]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL"],
)
def doubled(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


expr = doubled(orders)  # proves all three postconditions, then returns the expression
print(doubled.last_report)
# requires orders: (_.amount >= 0)
# requires orders: _.id.notnull()
# ensures (_.doubled >= 0): proved
# ensures _.doubled.notnull(): proved
# ensures id IS NOT NULL: proved
# known about the output:
#   id: any integer
#   doubled: an integer ≥ 22
```

A postcondition that doesn't follow is refused, along with what *is* known:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
def plus_one(orders):
    return orders.select(orders.id, total=orders.amount + 1)


plus_one(orders)
# VerificationError: could not prove: (_.total > 5) (it is TRUE or FALSE)
#   known about the output: total: an integer ≥ 1
```

* **Conditions** are Ibis expressions (`_.amount >= 0`) or SQL snippets (`"amount >= 0"`).
* **Preconditions** describe data that comes from outside. When the inputs are
  real tables, they are checked on the data at call time and raise
  `PreconditionError` if violated.
* **Unproved postconditions** raise `VerificationError`. With
  `on_unproved="runtime"` they are checked on the output data instead, and with
  `on_unproved="warn"` you get a warning.
* **Keys:** `sv.unique("user_id", "ts")` says there is at most one row per key.
  In `requires` it is checked on the data; in `ensures` it is proved.
* **Window functions:** `LAG`, `LEAD` and `ROW_NUMBER` are supported. Orderings
  that can tie are refused, because the engine would be free to pick either order.
* **ASOF joins:** `sv.asof_join` aligns sensors with different sampling rates,
  matching each row with the latest earlier row of the other table.
* **Not tracked yet:** string contents, DECIMAL columns, relations between columns
  beyond "column plus constant", and counts across rows.

## How do I know it's right?

* **Proofs.** The delta plan comes from a Lean function, with a theorem saying
  it computes exactly the change to the result. Contracts are decided by an
  analysis that is proven sound against the same semantics, which includes SQL's
  three-valued NULL logic.
* **Randomized tests.** Random tables and batches of changes, including NULLs
  and duplicates, check the parts the proofs don't cover: the translation of
  DataFusion's plans, the Python glue and the engine itself.

The repository's
[README](https://github.com/AlexanderNenninger/substrait-lean#readme) has the
full list of proven theorems, and explains what is trusted and what is proved.

## Configuration

* `SVERIFY_CHECK`: path to a `substrait-check` binary to use instead of the
  bundled one, for example your own `lake build`.
* `sverify` pins `datafusion==51.0.0`, because Ibis 12's DataFusion backend
  doesn't connect to later versions.

## Development

```bash
git clone https://github.com/AlexanderNenninger/substrait-lean
cd substrait-lean/python
uv sync                          # builds substrait-check with lake (needs elan) and links it in
uv run poe qa                    # proofs, lint, typecheck, golden and Python tests
```

See the [repository](https://github.com/AlexanderNenninger/substrait-lean) for setup details.

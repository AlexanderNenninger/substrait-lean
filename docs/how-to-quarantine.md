# Bad rows: quarantine and hold

The examples on this page run in order (`python/tests/test_readme.py`), from this setup:

```python
import ibis
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify.io import Changes, StaticSource

orders = StaticSource(
    pa.table({"id": [1, 2], "customer": ["ada", "bob"], "amount": [30, 5]}), name="orders"
)
orders.apply(Changes(inserts=[(3, "cy", 50)], deletes=[(1, "ada", 30)]))  # now orders holds bob and cy
from sverify.io import DeltaSink, DeltaSource
```

A batch that breaks a precondition on a source raises `PreconditionError` by
default, and the refresh commits nothing. `on_violation` on the transform, or
on the source, chooses otherwise:

- `"quarantine"` sets the rows that break a precondition aside, with the
  reason, and the node runs on the others.
- `"hold"` commits nothing for the batch and holds the node at its
  versions. The next refresh reads the batch again, so a fix upstream lets it
  through.
- `"error"` is the default.

The transform's setting holds over the source's. Where two transforms fused
into one node state the same condition, the stricter setting holds: error,
then hold, then quarantine.

```python
from deltalake import write_deltalake

write_deltalake(
    "lake/raw_orders",
    pa.table({"id": [1, 2, 3, 3], "customer": ["ada", "bob", "cy", "dee"], "amount": [30, -5, 7, 8]}),
)


@sv.transform(
    requires={"orders": [_.amount >= 0, sv.unique("id")]},
    ensures=[_.amount >= 0, sv.unique("id")],
    on_violation="quarantine",
)
def clean(orders):
    return orders.select("id", "customer", "amount")


raw = DeltaSource("lake/raw_orders", name="orders")
node = raw.pipe(clean).write(DeltaSink("lake/clean"))
r = node.refresh()
print(r)
# clean:
#   computed
# ...
#   quarantine: orders: 3 row(s) quarantined (1 × (_.amount >= 0), 2 × unique(id)), 3 in quarantine at lake/clean_quarantine
# ...
r.outcome           # "quarantined"
node.quarantined()  # the rows set aside, with _conditions, _reason, _source_version
```

Which rows are set aside is a function of the source's rows alone, so a
refresh batch by batch and a recompute agree:

- A row on which a row condition is FALSE or NULL (ranges, NOT NULL, value
  sets, inferred bounds).
- Among the other rows, every row of a key that occurs on more than one
  distinct row (`sv.unique`, `sv.key`): both rows of a repeated `id` with
  different values, the one the node held before included. Rows identical in
  every column count once: a redelivered duplicate of a kept row is set aside
  beside it, and the kept row stays. The rule needs no order between rows, so it gives the
  same answer under every profile ([tie order](reference-semantics.md#tie-order-and-determinism)).
- `max_rows`, `arrives_within` and the other conditions on a table as a whole
  have no rule for which rows break them. A batch that breaks one holds the
  node, as `"hold"` does, and the report says why.

Every precondition holds on the rows kept: Lean proves it for this rule
(on the snapshot with identical rows collapsed, see [proved-theorems.md](proved-theorems.md)),
so the node's contract holds on what it reads. The batch checks then run on the kept rows as on any batch, and a row
the rule let through by mistake would raise.
[`tests/test_quarantine.py`](../python/tests/test_quarantine.py) compares
every refresh of random batches with the rule.

A fix upstream releases rows. A delete or an update of a row set aside takes
it out of the quarantine, and the updated row is judged again. A key that is
on one row again lets that row through. The report counts what each refresh
set aside, released and saw deleted upstream.

A stored node writes the rows it sets aside to a table next to its sink: the
sink's URI, or Iceberg identifier, with `_quarantine` appended.
`.write(sink, quarantine=DeltaSink(...))` names another one, and
`quarantine=False` keeps the rows in memory. The table has one row per
distinct row set aside: the source, the row as JSON, its copies, the
conditions it breaks, the reason, the source version that set it aside, when,
and the node. Each write records the node's epoch and source versions, and
is written before the node's sink, so the table never lags the data it
explains. Its format is stable within 1.x ([stability](stability.md)).

`Refresh.outcome` is `"ok"`, `"quarantined"` (rows are set aside) or
`"held"` (a node skipped a batch), for a job's exit code. `Refresh.alert()`
gives a short Markdown text for whoever is on call: what broke, how many
rows, where they are, and what to do. `Refresh.to_json()`
gives the whole refresh as JSON
([`refresh.schema.json`](../python/src/sverify/schemas/refresh.schema.json)).
Both leave the rows themselves out, since they go to CI artifacts and
issues that more people read than read the data: `alert(rows=True)` shows
five as a table, `to_json(examples=True)` writes up to ten per source in
`examples`, and `PreconditionError.rows` and `QuarantineReport.examples`
hold them in the process.

A change to the schema that a contract cannot follow raises `SchemaError`,
and its message names the column, the version and the contract:

```text
`orders.id` became nullable at v12, and the new rows have NULLs in it; `paid`
requires _.id.notnull(). Fix the upstream, or handle NULLs in `paid` (e.g.
`.fill_null(0)`) and relax `requires`.
```

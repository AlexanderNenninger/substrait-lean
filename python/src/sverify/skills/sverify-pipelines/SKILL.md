---
name: sverify-pipelines
description: >
  Build incrementally maintained, contract-carrying data pipelines over Delta
  Lake or Iceberg tables with sverify. Use when a user wants to keep a query
  result up to date from a table's change feed instead of recomputing it,
  replace a watermark ("rows newer than…") job, write results to a Delta or
  Iceberg table exactly once, resume a restarted job, or prove preconditions
  from table metadata.
---

# sverify pipelines: Delta and Iceberg, kept up to date

A `sv.Pipeline` reads sources, maintains views over them, and refreshes them
from the sources' changes. Views in the incremental fragment (filters,
projections, inner and cross joins, `UNION ALL`) are updated by delta plans
proved equal to a full recompute; other views (left joins, aggregates,
windows, `DISTINCT`, `LIMIT`) are recomputed and diffed, and
`pipe.fallbacks` lists them. Needs the `delta` or `iceberg` extra.

## Source, contracted view, sink

```python
import datetime as dt
from pathlib import Path
from tempfile import mkdtemp

import ibis
import pyarrow as pa
from deltalake import DeltaTable, write_deltalake
from ibis import _

import sverify as sv
from sverify.io import DeltaSink, DeltaSource

lake = Path(mkdtemp())
SCHEMA = pa.schema(
    [
        pa.field("id", pa.int64(), nullable=False),
        pa.field("amount", pa.int64(), nullable=False),
        pa.field("ts", pa.timestamp("us"), nullable=False),
    ]
)


def rows(*rs):
    return pa.Table.from_pylist([dict(zip(SCHEMA.names, r)) for r in rs], schema=SCHEMA)


write_deltalake(
    lake / "orders",
    rows((1, 30, dt.datetime(2026, 1, 1)), (2, 5, dt.datetime(2026, 1, 2))),
    configuration={"delta.enableChangeDataFeed": "true"},
)  # CDF on: refresh reads it
DeltaTable(lake / "orders").alter.add_constraint({"non_negative": "amount >= 0"})


@sv.transform(
    requires={"orders": [_.amount >= 0, sv.unique("id")]},
    ensures=[_.doubled >= 22, sv.unique("id")],
)
def big(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


pipe = sv.Pipeline(sv.connect())
orders = pipe.source("orders", DeltaSource(str(lake / "orders")))
view = pipe.view("big", big(orders))  # proves the contract, loads the snapshot
for p in pipe.preconditions:
    print(p)
# orders: unique(id) (checked on data)
# orders: (_.amount >= 0) (Delta constraint)

sink = DeltaSink(str(lake / "big"), view)
print(sink.write())  # creates the table; guarantees become NOT NULL / CHECK constraints
# big from orders@v1: created v2, 1 row(s) written, 0 deleted
```

## Refresh from the change feed

```python
t = DeltaTable(lake / "orders")
write_deltalake(t, rows((3, 50, dt.datetime(2026, 1, 3))), mode="append")
t.delete("id = 1")

report = pipe.refresh(audit=True)  # CDF v1→v3, delta plans, then compare with a recompute
print(report.sources[0])
# orders@v1→v3: 1 insert(s), 1 delete(s); Δ trusted as coming from Delta CDF v1→v3
assert view.rows() == [(3, 100)] == view.recompute()
sink.write()  # one MERGE commit; a retry of the same state is skipped
```

* `refresh()` is all or nothing: a batch that breaks a precondition raises
  `PreconditionError` and changes nothing; the next refresh retries.
* `audit=True` also compares the batch with the new snapshot and every view
  with a recompute before committing (`AuditError`).
* Where the change feed is gone (CDF off, files vacuumed), the pipeline
  diffs the changed files and says so in the report.

## Resume a restarted job from its sink

```python
stored = DeltaSource(str(lake / "big")).stored()
restarted = sv.Pipeline(sv.connect())
src = restarted.source(
    "orders", DeltaSource(str(lake / "orders")), version=stored.sources["orders"]
)
resumed = restarted.view("big", big(src), resume=stored)
print(resumed.resumed)
# resumed from .../big@v3
```

The stored rows are used only if the plan and source versions match what
the sink recorded; otherwise the view is computed and `resumed` says why.

## Gotchas

* Turn on Delta's Change Data Feed (`delta.enableChangeDataFeed`) or every
  refresh falls back to diffing.
* Keys are always checked on the data (neither format enforces them); other
  preconditions come from schema nullability, CHECK constraints and file
  statistics where possible.
* A sink needs a version for every input: wrap a plain lookup table in
  `sv.StaticSource(table, version=1)`.
* A view with a contract isn't re-planned when a source's schema changes in
  an incompatible way: `refresh` raises `SchemaError` and changes nothing.

## More

[references/table-formats.md](references/table-formats.md): Iceberg, file
pruning, static sources, a downstream job reading the sink's contract.

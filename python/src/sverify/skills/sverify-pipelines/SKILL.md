---
name: sverify-pipelines
description: >
  Build incrementally maintained, contract-carrying data jobs over Delta Lake
  or Iceberg tables with sverify. Use when a user wants to keep a query
  result up to date from a table's change feed instead of recomputing it,
  replace a watermark ("rows newer than…") job, store results in a Delta or
  Iceberg table exactly once, chain jobs through stored tables, resume a
  restarted job, or prove preconditions from table metadata.
---

# sverify jobs: Delta and Iceberg, kept up to date

A contracted transform (`@sv.transform`) called on a source builds a node;
transforms called on nodes compose. `node.write(sink)` stores a node, and
`node.refresh()` brings its whole lineage up to date, upstream first. Nodes
in the incremental fragment (filters, projections, inner and cross joins,
`UNION ALL`) are updated by delta plans proved equal to a full recompute;
others (left joins, aggregates, windows, `DISTINCT`, `LIMIT`) are recomputed
and diffed. Needs the `delta` or `iceberg` extra.

## Source, contracted transforms, sink

```python
import datetime as dt
from pathlib import Path
from tempfile import mkdtemp

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
    configuration={"delta.enableChangeDataFeed": "true"},  # refresh reads the CDF
)
DeltaTable(lake / "orders").alter.add_constraint({"non_negative": "amount >= 0"})


@sv.transform(
    requires={"orders": [_.amount >= 0, sv.unique("id")]},
    ensures=[_.doubled >= 22, sv.unique("id")],
)
def big(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


orders = DeltaSource(str(lake / "orders"))
stored = big(orders).write(DeltaSink(str(lake / "big")))  # proved here
first = stored.refresh()  # checks preconditions, computes, writes the sink
for p in first["big"].preconditions:
    print(p)
# orders: unique(id) (checked on data)
# orders: (_.amount >= 0) (Delta constraint)
```

The sink's table gets the proved guarantees as NOT NULL columns and CHECK
constraints, and the contract in the commit. A transform called on `stored`
reads the table as a versioned source and builds on that contract.

## Refresh from the change feed

```python
t = DeltaTable(lake / "orders")
write_deltalake(t, rows((3, 50, dt.datetime(2026, 1, 3))), mode="append")
t.delete("id = 1")

print(stored.refresh(audit=True))  # CDF v1→v3, delta plans, one MERGE commit
# big:
#   orders@v1→v3: 1 insert(s), 1 delete(s); Δ trusted as coming from Delta CDF v1→v3
# ...
assert stored.to_arrow().to_pylist() == [{"id": 3, "doubled": 100}]
```

* `refresh()` is all or nothing: a batch that breaks a precondition raises
  `sverify.errors.PreconditionError` and changes nothing (sinks included);
  the next refresh retries.
* `audit=True` also compares the batch with the new snapshot and every node
  with a recompute before committing (`sverify.errors.AuditError`).
* `refresh(engine="polars")` (or `"datafusion"`, `"spark"`, a Spark session)
  picks the engine at refresh time.
* Where the change feed is gone (CDF off, files vacuumed), the changed files
  are diffed, and the report says so.

## Restart a job, and refresh several outputs together

A restarted job builds the same nodes again; the first refresh resumes each
stored node from its sink's table instead of recomputing it, if the plan and
source versions match what the sink recorded:

```python
restarted = big(DeltaSource(str(lake / "orders"))).write(DeltaSink(str(lake / "big")))
print(restarted.refresh())
# big:
#   resumed from .../big@v3
# ...
assert restarted.to_arrow().to_pylist() == [{"id": 3, "doubled": 100}]
```

`sv.group(a, b).refresh()` refreshes several outputs against the same source
versions, sharing the stored nodes they read; `.status()` reports on each.

## Gotchas

* Turn on Delta's Change Data Feed (`delta.enableChangeDataFeed`) or every
  refresh falls back to diffing.
* Keys are always checked on the data (neither format enforces them); other
  preconditions come from schema nullability, CHECK constraints and file
  statistics where possible.
* A sink needs a version for every input: wrap an in-memory lookup table in
  `sverify.io.StaticSource(table, version=1, name="regions")`.
* Without a `.write` between transforms, they fuse into one plan and the
  intermediate rows are never stored. Write a node when another job reads
  it, or when recomputing it would be expensive.
* A node with a contract isn't re-planned when a source's schema changes
  incompatibly: `refresh` raises `sverify.errors.SchemaError` and changes
  nothing.

## More

[references/table-formats.md](references/table-formats.md): Iceberg, file
pruning, static sources, chaining jobs through stored tables.

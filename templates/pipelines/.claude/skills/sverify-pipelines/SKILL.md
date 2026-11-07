---
name: sverify-pipelines
description: >
  Build incrementally maintained, contract-carrying data jobs over Delta Lake
  or Iceberg tables with sverify. Use when a user wants to keep a query
  result up to date from a table's change feed instead of recomputing it,
  replace a watermark ("rows newer than…") job, store results in a Delta or
  Iceberg table exactly once, chain jobs through stored tables, resume a
  restarted job, prove preconditions from table metadata, read from an API
  or a folder of files, write to a sink of their own, or set up credentials.
---

# sverify jobs: Delta and Iceberg, kept up to date

A contracted transform (`@sv.transform`) called on a source builds a node;
transforms called on nodes compose. `node.write(sink)` stores a node, and
`node.refresh()` brings its whole lineage up to date, upstream first. Nodes
in the incremental fragment (filters, projections, inner, cross, semi and
anti joins, `UNION ALL`, `DISTINCT`, `COUNT`, exact `SUM`/`AVG` and
`MIN`/`MAX` per group) are updated by delta plans proved equal to a full
recompute; other aggregates recompute only the groups a batch touches,
windows on one `PARTITION BY` the touched partitions (inputs without ties),
and bounded `RANGE` frames the touched frames; others (left joins, `LIMIT`)
are recomputed and diffed. `node.status()` says which
([guide](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/guide.md#nodes-composing-storing-refreshing)).
Needs the `delta` or `iceberg` extra.

A node whose contract is not proved refuses the refresh
(`UnverifiedRunError`, a `VerificationError`, "not verified: …");
`refresh(unverified=True)`, or `on_unproved="warn"` on its transform, runs it
anyway and records the route `"unverified"`. A sink accepts doubles within the plan's proved
bound by default (`sv.equivalent(floats="plan")`); `reproducible=sv.equivalent()`
asks for the same bits on a rerun.

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
    requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, sv.unique("id")]},
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
* `refresh(engine="polars")` (or `"spark"`, a Spark session) picks the
  engine at refresh time; `"datafusion"` also runs, experimental.
* `refresh().summary()` gives one line per node for the log of a job that
  refreshes often; `str(refresh)` is the full report.
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

A sink that writes every minute gathers commits and small files. Give the
`DeltaSink` its maintenance:

```python
minutely = DeltaSink(
    str(lake / "big_minutely"),
    checkpoint_interval=10,
    log_retention=dt.timedelta(days=7),
    compact_every=60,
    vacuum_retention=dt.timedelta(days=1),
)
```

`compact_every=60` compacts after every 60 writes, and `vacuum_retention`
then removes the files no version from the last day needs; `sink.maintain()`
does both by hand. The maintenance commits carry the contract. A restarted
job resumes past them, and past another writer's `OPTIMIZE`, `VACUUM` or
property change (an Iceberg sink past `replace` snapshots).

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

[references/custom-io.md](references/custom-io.md): your own sources (an
API, files, `from_query`, `from_frame`) and sinks (`Sink`, `sink_from`), and
credentials for S3, GCS, Azure and Iceberg catalogs (`Storage`).

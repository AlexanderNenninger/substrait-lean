# Table formats in more depth

## Iceberg

`IcebergSource(catalog, "db.table")` and `IcebergSink` work like their Delta
counterparts. Versions are snapshot sequence numbers; a run of appends is
read from the files those snapshots added, and anything else (row-level
deletes, overwrites) is a diff of the data files that changed. Iceberg has no
CHECK constraints, so the sink keeps the contract in the table properties and
snapshot summaries. Tables with equality deletes can't be read.

```python
import datetime as dt
import tempfile
import warnings

import pyarrow as pa
from ibis import _
from pyiceberg.catalog.sql import SqlCatalog

import sverify as sv
from sverify.io import IcebergSink, IcebergSource

warnings.filterwarnings("ignore", module="pyiceberg")
d = tempfile.mkdtemp()
catalog = SqlCatalog("lake", uri=f"sqlite:///{d}/catalog.db", warehouse=f"file://{d}")
catalog.create_namespace("plant")
READING = pa.schema(
    [
        pa.field("device_id", pa.int64(), nullable=False),
        pa.field("ts", pa.timestamp("us"), nullable=False),
        pa.field("temperature", pa.float64()),
    ]
)


def readings(*rs):
    return pa.Table.from_pylist([dict(zip(READING.names, r)) for r in rs], schema=READING)


table = catalog.create_table("plant.readings", schema=READING)
table.append(
    readings(
        (1, dt.datetime(2026, 7, 1, 12, 0), 31.0), (2, dt.datetime(2026, 7, 1, 12, 0), float("nan"))
    )
)


@sv.transform(
    requires={"readings": [sv.unique("device_id", "ts")]},
    ensures=[_.temperature > 30, ~_.temperature.isnan()],
)
def hot(readings):
    t = readings.temperature
    return readings.filter((t > 30) & ~t.isnan())


hot_readings = hot(IcebergSource(catalog, "plant.readings", name="readings"))
stored = hot_readings.write(IcebergSink(catalog, "plant.hot"))
stored.refresh()
table.append(readings((1, dt.datetime(2026, 7, 1, 12, 1), 33.0)))
print(stored.refresh())
# hot:
#   readings@v1→v2: 1 insert(s), 0 delete(s); Δ trusted as the files Iceberg appends v1→v2 added
# ...
assert len(stored.to_arrow()) == 2
```

`NaN > 30` is TRUE in SQL (NaN sorts above every number), which is why the
filter and the postcondition rule NaN out explicitly.

## Proved file pruning (Delta)

`DeltaSource(uri, where="amount * 2 > 100")` reads only the rows on which the
condition is TRUE, and skips a file only if Lean proves from its statistics
that no row of it can match. Changes are filtered the same way, and the
condition becomes a fact the contracts can use.

## Tables outside a table format

A sink writes exactly once per state, keyed by the versions of all its
inputs. A small lookup table that lives in memory becomes a source with a
version you choose; `apply` changes some of its rows, and `replace` swaps
the whole table (the next refresh diffs it):

```python
from sverify.io import StaticSource

regions = StaticSource(
    pa.table({"device_id": [1, 2], "region": ["north", "south"]}), version=1, name="regions"
)


@sv.transform()
def located(readings, regions):
    return readings.join(regions, readings.device_id == regions.device_id).select(
        readings.ts, regions.region
    )


where = located(IcebergSource(catalog, "plant.readings", name="readings"), regions)
where.refresh()
regions.replace(pa.table({"device_id": [1, 2], "region": ["north", "east"]}), version=2)
where.refresh()  # recomputes from the new regions
assert sorted(set(where.to_arrow().column("region").to_pylist())) == ["east", "north"]
```

## Chaining jobs through stored tables

A transform called on a written node reads its table as a versioned source
and builds on the contract the sink stored (Delta: NOT NULL columns and CHECK
constraints), instead of checking the data again:
`revenue(paid(orders).write(DeltaSink(...))).write(DeltaSink(...))`. A
separate job that opens the table with `DeltaSource(uri)` gets the same:
`DeltaSource(uri).contract()` returns the contract, and each refresh report
names where every precondition came from.

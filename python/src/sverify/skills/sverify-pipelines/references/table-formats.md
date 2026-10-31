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


pipe = sv.Pipeline(sv.connect())
view = pipe.view("hot", hot(pipe.source("readings", IcebergSource(catalog, "plant.readings"))))
sink = IcebergSink(catalog, "plant.hot", view)
sink.write()
table.append(readings((1, dt.datetime(2026, 7, 1, 12, 1), 33.0)))
print(pipe.refresh().sources[0])
# readings@v1→v2: 1 insert(s), 0 delete(s); Δ trusted as the files Iceberg appends v1→v2 added
sink.write()
assert len(view.rows()) == 2
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
version you choose:

```python
regions = sv.StaticSource(pa.table({"device_id": [1, 2], "region": ["north", "south"]}), version=1)
pipe2 = sv.Pipeline(sv.connect())
r = pipe2.source("readings", IcebergSource(catalog, "plant.readings"))
g = pipe2.source("regions", regions)
located = pipe2.view("located", r.join(g, r.device_id == g.device_id).select(r.ts, g.region))
regions.replace(pa.table({"device_id": [1, 2], "region": ["north", "east"]}), version=2)
pipe2.refresh()  # recomputes the views that read `regions`
assert sorted({row[1] for row in located.rows()}) == ["east", "north"]
```

## A downstream job builds on the sink's contract

A job that reads a sink's table gets its preconditions from the contract the
sink wrote (Delta: NOT NULL columns and CHECK constraints), instead of
checking the data again. `DeltaSource(uri).contract()` returns it, and
`pipe.preconditions` names where each precondition came from.

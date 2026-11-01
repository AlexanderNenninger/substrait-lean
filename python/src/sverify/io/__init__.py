"""Sources and sinks: Delta Lake and Iceberg tables, in-memory tables, and
the ones you write yourself, as the inputs and the stored results of
transforms, carrying proved contracts between jobs.

    import sverify as sv
    from sverify.io import DeltaSink, DeltaSource

    orders = DeltaSource("s3://lake/orders")
    p = paid(orders).write(DeltaSink("s3://lake/paid"))
    r = revenue(p).write(DeltaSink("s3://lake/revenue"))
    print(r.refresh())   # orders@v3→v5: ...; Δ trusted as coming from Delta CDF v3→v5

Sources hand Arrow tables to the transforms, so every engine works. A sink
stores a node exactly once per state, with its contract (`Contract`), and
reports what each write did (`SinkWrite`); nodes downstream read the stored
table as a versioned source. A `StaticSource` is an in-memory table with
versions the caller gives. Each table format is an extra:
`pip install 'sverify[delta]'` or `'sverify[iceberg]'`; its classes are
imported when first used. `Storage` holds object store options (credentials,
region) shared by several tables.

Your own sources and sinks:

* A `Source` subclass implements `read(since)`, which returns the new rows
  and a cursor as a `Batch`; `from_query` (rows by a high-water mark),
  `from_frame` (the whole table on every refresh) and `from_files` (new
  files in a directory) build one from a function or a path.
* A `Sink` subclass implements `write(change)`, which stores a
  `SinkChange`, and optionally `committed()`, which reads back the last
  contract, so states are written exactly once across restarts.
  `sink_from(fn)` hands the whole table to a function.
* A table format with metadata and a change feed implements the full
  `VersionedSource` protocol: `Snapshot` and `SourceBatch` are what it
  returns.
"""

from __future__ import annotations

import importlib
from typing import TYPE_CHECKING, Any

from sverify.incremental import Snapshot, SourceBatch, StaticSource, VersionedSource
from sverify.io._common import Contract, SinkWrite
from sverify.io._sink import Sink, SinkChange, sink_from
from sverify.io._source import Batch, Source, from_files, from_frame, from_query
from sverify.io._storage import Storage

if TYPE_CHECKING:
    from sverify.io.delta import DeltaSink, DeltaSource
    from sverify.io.iceberg import IcebergSink, IcebergSource

_MODULES = {
    "DeltaSink": "delta",
    "DeltaSource": "delta",
    "IcebergSink": "iceberg",
    "IcebergSource": "iceberg",
}


def __getattr__(name: str) -> Any:
    if name not in _MODULES:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
    return getattr(importlib.import_module(f"sverify.io.{_MODULES[name]}"), name)


__all__ = [
    "Batch",
    "Contract",
    "DeltaSink",
    "DeltaSource",
    "IcebergSink",
    "IcebergSource",
    "Sink",
    "SinkChange",
    "SinkWrite",
    "Snapshot",
    "Source",
    "SourceBatch",
    "StaticSource",
    "Storage",
    "VersionedSource",
    "from_files",
    "from_frame",
    "from_query",
    "sink_from",
]

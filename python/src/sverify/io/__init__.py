"""Delta Lake and Iceberg tables as the sources and the stored results of
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
imported when first used.
"""

from __future__ import annotations

import importlib
from typing import TYPE_CHECKING, Any

from sverify.incremental import StaticSource
from sverify.io._common import Contract, SinkWrite

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
    "Contract",
    "DeltaSink",
    "DeltaSource",
    "IcebergSink",
    "IcebergSource",
    "SinkWrite",
    "StaticSource",
]

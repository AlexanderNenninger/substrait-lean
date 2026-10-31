"""Delta Lake and Iceberg tables as change sources, sources of
preconditions, and sinks that carry proved contracts between jobs.

    import sverify as sv
    from sverify.io import DeltaSource, DeltaSink

    pipe = sv.Pipeline(sv.connect())
    orders = pipe.source("orders", DeltaSource("data/orders"))
    big = pipe.view("big", doubled(paid(orders)))
    sink = DeltaSink("data/big", big)
    sink.write()
    ...
    print(pipe.refresh())   # orders@v3→v5: ...; Δ trusted as coming from Delta CDF v3→v5
    sink.write()

Sources hand Arrow tables to the pipeline, so every engine works. Each
format is an extra: `pip install 'sverify[delta]'` or `'sverify[iceberg]'`;
its classes are imported when first used.
"""

from __future__ import annotations

import importlib
from typing import TYPE_CHECKING, Any

from sverify.io._common import ColumnStats, Contract, stats_facts

if TYPE_CHECKING:
    from sverify.io.delta import DeltaSink, DeltaSource, SinkWrite
    from sverify.io.iceberg import IcebergSink, IcebergSource, IcebergWrite

_MODULES = {
    "DeltaSink": "delta",
    "DeltaSource": "delta",
    "SinkWrite": "delta",
    "IcebergSink": "iceberg",
    "IcebergSource": "iceberg",
    "IcebergWrite": "iceberg",
}


def __getattr__(name: str) -> Any:
    if name not in _MODULES:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
    return getattr(importlib.import_module(f"sverify.io.{_MODULES[name]}"), name)


__all__ = [
    "ColumnStats",
    "Contract",
    "DeltaSink",
    "DeltaSource",
    "IcebergSink",
    "IcebergSource",
    "IcebergWrite",
    "SinkWrite",
    "stats_facts",
]

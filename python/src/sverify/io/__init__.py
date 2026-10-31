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

Sources hand Arrow tables to the pipeline, so every engine works.
"""

from sverify.io._common import ColumnStats, Contract, stats_facts
from sverify.io.delta import DeltaSink, DeltaSource, SinkWrite

__all__ = ["ColumnStats", "Contract", "DeltaSink", "DeltaSource", "SinkWrite", "stats_facts"]

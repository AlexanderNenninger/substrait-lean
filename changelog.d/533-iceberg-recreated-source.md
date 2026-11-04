### A recreated Iceberg source no longer leaves its sinks stale

An Iceberg table dropped and created again under the same identifier is
another table, even where its sequence numbers reach the old ones. An
`IcebergSource` now records the table's UUID with each version it reads,
and sinks record it in their contract (`Contract.table_ids`), as Delta
sources do with their table id since
[#516](https://github.com/AlexanderNenninger/substrait-lean/issues/516). A
refresh then reads the new table in full, and a restarted job recomputes
its nodes instead of resuming from rows of the old table
([#533](https://github.com/AlexanderNenninger/substrait-lean/issues/533)).

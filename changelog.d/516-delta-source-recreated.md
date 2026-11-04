### A Delta source dropped and created again rewrites its sinks

A Delta source dropped and created again at the same path starts its
versions over. Its sinks had committed a higher epoch, so each refresh
skipped the write as "already committed" and kept the old table's rows,
with no error, in the same process and after a restart
([#516](https://github.com/AlexanderNenninger/substrait-lean/issues/516)).

The contract now records each Delta source's table id (`metaData.id`,
`Contract.table_ids`). When a source's id changed, or its version went
down, the sink's rows come from another table: the refresh recomputes the
node and overwrites the sink, so it holds a full recompute of the new
table. `DeltaSource.changes` reads the new table's snapshot when the table
was created again since the version asked for (the report says
"created again"), and a restarted job doesn't resume from a state stored
from the old table.

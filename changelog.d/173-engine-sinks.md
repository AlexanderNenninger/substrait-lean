### DuckDB writes Delta and Iceberg sinks

When a node runs on DuckDB, its `DeltaSink` and `IcebergSink` have DuckDB
write the Parquet files, and sverify commits them with the contract and the
epoch, exactly once as before. The state and the rows never pass through
Python. A Delta change rewrites only the files that hold deleted rows and
adds a file of the new rows, in one commit with delta-rs's statistics; an
Iceberg change is a data file with field ids and a position delete file.
Other engines, partitioned or remote tables, and an overwrite by another
plan write through delta-rs and pyiceberg as before.

A Delta sink no longer mistakes its own constraint for a foreign one when the
node's guarantee has a decimal number: Delta stores `x >= 0.0` as `x >= 0`
(#173).

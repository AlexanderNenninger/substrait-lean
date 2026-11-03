### Delta sinks maintain their tables and resume past maintenance

`DeltaSink` takes `checkpoint_interval`, `log_retention`, `compact_every`
and `vacuum_retention`, and `DeltaSink.maintain()` compacts and vacuums by
hand. The maintenance commits carry the contract of the sink's last commit.
A restarted job now resumes from a table whose commits after the sink's
last one change no rows: `OPTIMIZE`, `VACUUM`, property and constraint
changes, by `maintain` or another writer. It used to recompute the node and
overwrite the table. An Iceberg sink resumes past `replace` snapshots
likewise (#377).

delta-rs 1.6.6 hangs in `history()` and `set_table_properties()` against an
S3 server in the same Python process, such as moto's `ThreadedMotoServer`
(`upstream/LEDGER.md` DL-1). Run moto as its own process.

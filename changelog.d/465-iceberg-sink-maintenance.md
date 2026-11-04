### An Iceberg sink maintains its table

A streaming `IcebergSink` used to add a snapshot, a data file and a position
delete file on every refresh, so a two-row aggregate refreshed every minute
grew by some 1,440 snapshots and 2,900 files a day. `IcebergSink` now takes
`DeltaSink`'s maintenance options: `compact_every=N` compacts the table after
every N writes, rewriting the data files with position deletes and the small
files of each partition as data files of their live rows in one `replace`
snapshot, and dropping the delete files no data file reads.
`snapshot_retention=` then expires older snapshots (keeping `min_snapshots`
and the sink's own last one) and deletes the files only they referenced.
`maintain()` runs it on demand. The compaction snapshot carries the contract,
so a restarted job resumes past it, and downstream nodes read through it. With
`compact_every=4`, an aggregate refreshed 37 times holds at most 5 snapshots,
4 data files, 3 delete files and 41 files on disk, and equals a full
recompute throughout (`test_maintenance_keeps_a_streaming_sink_bounded`)
([#465](https://github.com/AlexanderNenninger/substrait-lean/issues/465)).

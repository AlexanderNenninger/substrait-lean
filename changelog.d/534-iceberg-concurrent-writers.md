### Two writers of one `IcebergSink` no longer apply a change twice

An `IcebergSink` now commits only while the table still holds the epoch it
read, as a `DeltaSink` does since
[#517](https://github.com/AlexanderNenninger/substrait-lean/issues/517). When
two processes refresh the same sink, the one that commits second raises
`ConcurrentWriteError`, also where pyiceberg would retry its commit on top
of the other writer's snapshot, and where both create the table. Its next
refresh writes the whole table, or skips the state the other writer
committed
([#534](https://github.com/AlexanderNenninger/substrait-lean/issues/534)).

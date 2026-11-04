### Two processes refreshing the same `DeltaSink` no longer write a change twice

`DeltaSink` read the epoch the table had committed, then loaded the table
again and committed, so a commit by another process in between went
unnoticed. Two pods of one job during a rolling deploy, or a cron run
overlapping a slow one, could both write the same change, or write an older
change on top of a newer state, and later refreshes kept the duplicate rows
([#517](https://github.com/AlexanderNenninger/substrait-lean/issues/517)).

The commit is now conditional. It is made on a snapshot whose transaction
version (`app_id`) is still the one the refresh read, and every commit that
changes rows carries the transaction, so delta-rs's conflict check rejects a
concurrent one. The process that loses raises
`sverify.errors.ConcurrentWriteError`, naming the sink, and its write is not
committed. Its next refresh skips the state the other process committed, or
writes the whole table. This holds for local (native) commits and for
MERGE. A sink of your own raises the same error to get the same recovery.

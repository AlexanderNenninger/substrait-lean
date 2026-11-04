### A partitioned Iceberg sink takes only the change

An `IcebergSink` whose table is partitioned (identity, `day()` or any other
transform) writes each refresh as one snapshot of position deletes and new
rows in the partitions the change touches, as an unpartitioned table
already did ([#43](https://github.com/AlexanderNenninger/substrait-lean/issues/43)).
It used to overwrite the whole table in two snapshots on every refresh. The
deletes read only the data files of the partitions the deleted rows fall
in, each delete file is in the partition of its data file, and the other
partitions keep their files. Rows are split by partition without
`pyiceberg-core`, which pyiceberg 0.12 needs for every transform but
`identity`, so a `day()`-partitioned sink also works without it
([#466](https://github.com/AlexanderNenninger/substrait-lean/issues/466)).

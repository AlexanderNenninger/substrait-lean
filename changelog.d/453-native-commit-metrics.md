### A local `DeltaSink`'s commits log what they changed

A `DeltaSink` on a local path commits the files DuckDB wrote, and the Delta
history showed that commit as a `WRITE` with no `operationMetrics`, while
the same refresh on S3, a delta-rs MERGE, logged the rows it inserted and
deleted ([#453](https://github.com/AlexanderNenninger/substrait-lean/issues/453)).
The local commit now logs a write's metrics (`num_added_rows`,
`num_added_files`, `num_removed_files`, …) and, for a change, the ones
delta-rs's MERGE logs (`num_target_rows_inserted`,
`num_target_rows_deleted`, `num_target_rows_copied`,
`num_target_files_added`, …), with `operationParameters.sverify` set to
`merge` or `created`. The operation stays `WRITE`: delta-rs 1.6.6 refuses
another name.

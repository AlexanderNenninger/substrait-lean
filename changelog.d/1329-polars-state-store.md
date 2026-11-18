### Polars keeps a pipeline view's state in Parquet files it writes and scans

On Polars, an incremental view's state is a generation of Parquet files that Polars writes and scans lazily, where it was an Arrow table in the Python process (#1329, #173). Merging a change into the state runs the merge plan on Polars. The Polars translation takes `rows="multiset"` (as `to_sql` does), which lets an aggregate emit its groups in any order: the merge of a state peaks at 651 MB where it peaked at 1078 MB for two million rows.

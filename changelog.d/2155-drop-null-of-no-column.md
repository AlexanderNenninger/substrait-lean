### `drop_null` of no column verifies

An Ibis `drop_null([])` (an empty subset, or a table with no column to test) no longer crashes the producer with an `IndexError` ([#2155](https://github.com/AlexanderNenninger/substrait-lean/issues/2155)). With `how="any"` every row stays; with `how="all"` none does, as DuckDB gives.

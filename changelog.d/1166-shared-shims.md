### Shims the engines share are proved once, as `Shim.*`

The lemmas for shims that several engines' translations write the same way
moved from `Polars.*` (and Spark's copies of them) to `Shim.*` in
`SubstraitLean/Shims.lean`: `one_zero` (`-0.0` as `0.0`), `null_order`,
`sum_empty_null`, `avg_trunc` (an integer `AVG` as the truncated mean) and
`makes_infinite` (#1166). DuckDB's, Polars's and Spark's rows cite them,
so `--options` and the realizability table name `Shim.one_zero` where they
named `Polars.one_zero` or `Spark.one_zero`.

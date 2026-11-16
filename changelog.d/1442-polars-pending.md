### `semantics="polars"` is reported as pending

The checker does not report under Polars's own profile yet, as for Spark
([#1288](https://github.com/AlexanderNenninger/substrait-lean/issues/1288)).
`verify(semantics="polars")` now gives the reference's report with a
`ProfilePendingWarning` (`report.semantics` says `"reference"`), and the plan
reaches Polars by the `translated` route, which shims integer `%` to truncate.
The `native` route to Polars and the `recheck` route from a DuckDB report to
Polars are refused until the checker proves under `Profile.polars`
([#1442](https://github.com/AlexanderNenninger/substrait-lean/issues/1442)).
Polars's observation rows now apply to Polars's tables.

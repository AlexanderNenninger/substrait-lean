### The reference semantics is the default everywhere

Breaking: `sv.sql(query)` now uses sverify's reference semantics by default,
as `sv.verify` and `@sv.transform` do; DuckDB's semantics (NaN and ±inf as
DuckDB computes them) is an explicit opt-in, `semantics="duckdb"` (#411).
Write `semantics="duckdb"` on `sv.sql` calls that relied on the old default.
SQL transformations and SQL conditions in `sv.verify` and `@sv.transform`
were lifted with DuckDB's semantics too, and now follow the new `semantics=`
parameter of each, which defaults to the reference. `Report.semantics`, and a
`semantics:` line in the printed report, say which semantics a check used.

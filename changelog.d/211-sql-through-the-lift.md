### SQL strings are DuckDB's SQL, through sverify's own lift

`sv.sql`, `sv.verify` of a SQL string, SQL conditions in contracts, Ibis's
`Table.sql` and `Backend.sql`, and `sverify.engines.substrait_json` now read
**DuckDB's SQL** and plan it with sverify's own SQLGlot lift
(`sverify.sql_lift`, #239). DataFusion's SQL planner is gone as a frontend
(#211); DataFusion stays an execution backend (`engine="datafusion"`), and SQL
strings no longer need the `datafusion` extra.

This changes what some SQL means. In DuckDB's SQL, `/` divides as doubles
(`7 / 2` is 3.5; integer division is `//`), `1.5` is a `DECIMAL(2, 1)` rather
than a double, and NULLs sort last in both directions. A double divided by
zero raises under the reference semantics, the default (#411), and is `±inf`
or NaN with `semantics="duckdb"`. The entries for #240 list what the lift
reads; anything else is refused, saying what. Write those queries in Ibis
meanwhile.

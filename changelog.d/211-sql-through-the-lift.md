### SQL strings are DuckDB's SQL, through sverify's own lift

`sv.sql`, `sv.verify` of a SQL string, SQL conditions in contracts, Ibis's
`Table.sql` and `Backend.sql`, and `sverify.engines.substrait_json` now read
**DuckDB's SQL** and plan it with sverify's own SQLGlot lift
(`sverify.sql_lift`, #239). DataFusion's SQL planner is gone as a frontend
(#211); DataFusion stays an execution backend (`engine="datafusion"`), and SQL
strings no longer need the `datafusion` extra.

This changes what some SQL means. In DuckDB's SQL, `/` divides as doubles
(`7 / 2` is 3.5; integer division is `//`), `1.5` is a `DECIMAL(2, 1)` rather
than a double, NULLs sort last in both directions, and a double divided by
zero is `±inf` or NaN. `sv.sql(query, semantics="reference")` reads the same
text with sverify's reference semantics instead (a double divided by zero
raises). The lift reads a subset of SQL so far: SELECT, WHERE, inner, left
and cross joins, subqueries in FROM, GROUP BY with `count`, `sum`, `avg`,
`min` and `max`, HAVING, DISTINCT, ORDER BY, LIMIT, CASE, CAST, COALESCE,
`date_trunc` and arithmetic. Anything else is refused, saying what; the
rest follows in M2 (#240). Write those queries in Ibis meanwhile.

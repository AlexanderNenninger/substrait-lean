### The SQL lift reads CTEs, subqueries and more joins

The SQL lift now reads (#240):
- **CTEs:** non-recursive `WITH`, inlined where each is read; a later CTE may read an earlier one.
- **Uncorrelated subqueries:** a scalar subquery (the checker must prove it has at most one row: an aggregate without groups, or `LIMIT 1`), `x [NOT] IN (SELECT …)` with SQL's rules for NULLs, and `EXISTS (…)`.
- **More joins:** `SEMI`, `ANTI`, `RIGHT` and `FULL` joins.

A subquery that reads a column of the query around it (a correlated subquery) is refused, saying so; write it as a join, or as a `SEMI` or `ANTI` join.

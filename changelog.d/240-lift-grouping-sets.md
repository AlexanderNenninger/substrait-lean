### The SQL lift reads GROUPING SETS, ROLLUP and CUBE

The SQL lift now reads `GROUP BY` with `GROUPING SETS`, `ROLLUP` and `CUBE`, alone or next to plain keys, and `GROUPING(…)` in the select list, HAVING, ORDER BY and window functions (#240). Each grouping set becomes its own aggregate, with NULL for the keys the set leaves out and the value of each `GROUPING(…)` as a constant. The aggregates are joined with `UNION ALL`, as DuckDB computes them. On empty input, the empty set's grand-total row is kept.

Two fixes came with it:
- A window function's `PARTITION BY` and `ORDER BY` may now be expressions, not only columns. The plan computes them as columns first, since the model reads them as columns.
- In an `ORDER BY` expression, a bare name is the output column of that name, as in DuckDB. For example, `ORDER BY CASE WHEN s > 0 THEN customer END` where `s` is an alias.

TPC-DS q27 and q36 now pass: 51 of 54 benchmark queries agree.

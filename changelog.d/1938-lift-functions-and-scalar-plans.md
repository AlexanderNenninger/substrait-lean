### SQL lift and plans without a table: more functions

The SQL lift reads `radians(x)` and `degrees(x)` (#1938), `right(s, n)` with a
column or expression for `n` (#1942), `str_split` inside the arguments of
another `str_split` (#1940) and a `WITH` in front of a `UNION`, `EXCEPT` or
`INTERSECT` (#1939). A plan that reads no table, as an Ibis scalar expression
makes, now runs on DuckDB (#1916); Polars refuses it, naming the construct.

Under `semantics="duckdb"`, the lifted integer `%` lists `MIN % -1` as an issue, since DuckDB raises there (#2058); a bound on either operand discharges it. DuckDB, Polars and Spark run the guard; an engine that cannot raise it refuses the plan and names it.

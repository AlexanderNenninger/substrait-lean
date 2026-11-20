### SQL lift and plans without a table: more functions

The SQL lift reads `radians(x)` and `degrees(x)` (#1938), `right(s, n)` with a
column or expression for `n` (#1942), `str_split` inside the arguments of
another `str_split` (#1940) and a `WITH` in front of a `UNION`, `EXCEPT` or
`INTERSECT` (#1939). A plan that reads no table, as an Ibis scalar expression
makes, now runs on DuckDB (#1916); Polars refuses it, naming the construct.

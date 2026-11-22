### Binary and map columns pass through

Sverify carries a column of a type it does not read, such as binary or a map,
through a plan unchanged on DuckDB, Polars and Spark: a `SELECT *` over a table
with a binary or map column, a filter or join on other columns, a sort on
others, `UNION ALL` and `LIMIT`. `IS NULL` and `IS NOT NULL` read such a column.
Any other use is refused, and the message names it: a function, comparison or
cast of the column, a filter, join, sort, grouping or partition on it, and
`DISTINCT` over it. A binary constant stays refused
([#1958](https://github.com/AlexanderNenninger/substrait-lean/issues/1958),
[#1918](https://github.com/AlexanderNenninger/substrait-lean/issues/1918)).

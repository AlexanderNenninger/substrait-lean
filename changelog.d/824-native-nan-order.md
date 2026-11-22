### Sorts by a double on DuckDB and Spark

The SQL Sverify writes for DuckDB and Spark sorts by a double column itself. It no longer adds a key that ranks NaN apart, since both engines already order NaN above `+inf` as the reference does (#824).

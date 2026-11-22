### Nanosecond timestamp columns are read

A `timestamp[ns]` column, the unit Parquet and pandas often carry, is read
with every digit on DuckDB and Polars. Sverify compares it with other
nanosecond timestamps, orders, groups and joins on it, counts it and takes its
`MIN` and `MAX`. Nanoseconds reach 1677-09-21 to 2262-04-11. A calendar
function, interval arithmetic, a cast, or a microsecond timestamp or literal in
the same comparison is refused, and the message says so. Spark holds
microseconds only and refuses the column
([#323](https://github.com/AlexanderNenninger/substrait-lean/issues/323)).

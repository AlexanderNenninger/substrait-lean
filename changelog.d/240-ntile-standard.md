### `NTILE` deals out buckets as SQL does

`NTILE(k)` now follows the SQL standard, as DuckDB, Spark and Snowflake
compute it: the first `n % k` buckets hold one row more. It used to follow
DataFusion's formula, which spreads the larger buckets out (`ntile(4)` of
10 rows gave `1 1 1 2 2 3 3 3 4 4`; now `1 1 1 2 2 2 3 3 4 4`). DataFusion
is refused for `NTILE` for now. `verify` still proves `1 ≤ NTILE ≤` the
row's number.

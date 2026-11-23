### A typed NULL beside a nested call keeps its type in the written plan

`CAST(NULL AS DOUBLE)` projected beside a nested call such as `-(d + d)` was written as an `i64` NULL, so Polars returned an `int64` column and DuckDB an untyped one. The written plan now keeps the declared type (#2102).

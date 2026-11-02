### Bit aggregates

`bit_and()`, `bit_or()` and `bit_xor()` of integers are verified: the
64-bit operation folded over the non-NULL values, NULL for a group without
one. They run on DuckDB, Polars, DataFusion, Spark (`BIT_AND`, …) and
Snowflake (`BITAND_AGG`, …) (#53).

### Lists run on DuckDB

Plans with lists now run on DuckDB as well as Polars (#94): list columns and
literals, list elements and `length`, `collect()` (ordered or not, NULLs
skipped) and `unnest`. The written SQL keeps Lean's order: each row's
elements come out in list order, and ties in a `collect` order fall to the
row order, so an order-dependent step above sees the same rows Lean does.
Snowflake and Spark still refuse lists, until #271; structs and lambdas stay
Polars-only for now.

### Repeated terms written once

A term a written plan computes in several places, `CASE` branches among
them, is now computed once as a column when the plan evaluates it on every
row anyway (#821, `Expr.repeated` in `SubstraitLean/Bind.lean`). Ibis's
`find` with a start drops from 66 kB of Snowflake SQL to 3 kB, and
`day_of_week.full_name()` from 11 kB to 2 kB on DuckDB and Spark.

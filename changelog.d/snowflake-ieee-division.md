### Snowflake: IEEE division by zero

On Snowflake, a division of doubles under `on_division_by_zero` = `IEEE` gives the reference's `±inf` or NaN for a zero divisor, where it raised: Snowflake's `/` raises on a zero divisor, so the result by zero is written out, as Spark's writer does.

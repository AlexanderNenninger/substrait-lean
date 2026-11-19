### Snowflake: a `-0.0` literal keeps its sign

Snowflake's SQL writes a `-0.0` literal as `CAST('-0.0' AS FLOAT)`, as the other writers keep a negative zero (D31), where it wrote `0.0`. A sign-sensitive use of the literal (`atan2(-0.0, -1.0)`) now gives the reference's value on Snowflake. The DuckDB and Polars facts on `round`, `floor` and `ceil` now state the reference's `round_zero_sign` (left open; `eval` gives `+0.0`) and `zero_sign` (`ONE_ZERO`).

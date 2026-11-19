### Snowflake: a `-0.0` literal keeps its sign

Snowflake's SQL writes double literals as the other writers do (the base writer's `float_lit`): a `-0.0` literal is `CAST('-0.0' AS FLOAT)` and keeps its sign (D31), where it was written `0.0`; infinities are spelt `'Infinity'`. A sign-sensitive use of the literal (`atan2(-0.0, -1.0)`) now gives the reference's value on Snowflake. The DuckDB and Polars facts on `round`, `floor` and `ceil` now state the reference's `round_zero_sign` (left open; `eval` gives `+0.0`) and `zero_sign` (`ONE_ZERO`).

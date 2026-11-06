### Engines run `SUM` and `AVG` of doubles natively

With the reference's correctly rounded sum (D25), no engine needs to add
doubles in Lean's order
([#917](https://github.com/AlexanderNenninger/substrait-lean/issues/917)).
DuckDB's SQL writes plain `SUM` where it emulated the order with
`list_reduce`, Spark's plain `SUM` where it sorted the values first, and
Snowflake and Spark no longer refuse a `SUM` or `AVG` of doubles, grouped or
not. Every engine's result is within the plan's bound of the reference
(`Report.epsilon`, `StdModel.epsilon_sum_cr`). A double `SUM` over 10⁷ rows on
DuckDB takes 0.02 s, down from 13.4 s. Windows over a Spark or Snowflake table
still need a proved `deterministic=True`, for their row order.

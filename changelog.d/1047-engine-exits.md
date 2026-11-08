### Engine and writer refusals name their exit

- Every refusal of the Polars translator, the DataFusion runner and the
  Spark and Snowflake SQL writers now ends with what to do next:
  `run it with engine='duckdb'` and the issue that tracks the engine, or a
  rewrite where one keeps the result (a cast to fewer digits for Spark's
  decimals). Before, "Spark window functions need an ORDER BY", "Snowflake's
  LN is not documented to be C's libm" or "DECIMAL(40, 2) is not a decimal
  type Polars has" named none
  ([#1047](https://github.com/AlexanderNenninger/substrait-lean/issues/1047)).
- A writer hook a dialect lacks reads "the spark writer does not write
  integer division yet: run it with engine='duckdb' (see #271, …)", in place
  of "spark: integer division is not implemented".

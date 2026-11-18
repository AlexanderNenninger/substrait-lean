### The refusal of `CAST(DOUBLE AS BIGINT)` no longer advises `round()` first

Under `semantics="duckdb"` the lift refuses `CAST(x AS BIGINT)` of a double, since DuckDB
rounds half to even and the model's cast truncates. The message advised `round()` first,
but the lift refuses that composition too. It now says to use `semantics='reference'`
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

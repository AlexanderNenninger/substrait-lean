### Spark runs window aggregates without an ORDER BY, and the variance over a frame

Spark runs an aggregate over a whole partition with no ORDER BY (`SUM(x) OVER (PARTITION BY k)`), and `VAR_*` and `STDDEV_*` over a window, as DuckDB does. Snowflake runs the first too. Ranking and offset functions still need an ORDER BY there ([#2540](https://github.com/AlexanderNenninger/substrait-lean/issues/2540)).

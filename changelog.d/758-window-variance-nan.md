### A windowed population variance of a lone NaN is NaN

`VAR_POP` and `STDDEV_POP` over a window frame whose only non-NULL value is
NaN gave `0.0` through the written SQL, where the reference (`varOf`) gives
NaN. DuckDB's population variance of one value is 0 whatever the value
([DD-3](upstream/bugs/DD-3.json), `duckdb-var-pop-one-value`). The SQL
writer already returned NaN for a group with a NaN; the window form now does
too ([#758](https://github.com/AlexanderNenninger/substrait-lean/issues/758)).

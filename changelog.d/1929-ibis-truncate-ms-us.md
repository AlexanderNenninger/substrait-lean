### Ibis reads `truncate("ms")` and `truncate("us")`

`ts.truncate("ms")` and `ts.truncate("us")` of a timestamp are read as `date_trunc('millisecond', …)` and `date_trunc('microsecond', …)`, which Lean, DuckDB, Polars and Spark already modelled ([#1929](https://github.com/AlexanderNenninger/substrait-lean/issues/1929)). Nanoseconds stay refused. The casts of a timestamp to a number and of a double to a timestamp stay refused by design: DuckDB has no such cast, and the replay ledgers record why ([#1922](https://github.com/AlexanderNenninger/substrait-lean/issues/1922)).

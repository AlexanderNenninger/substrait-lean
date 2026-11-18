### DuckDB's integer mean on x86-64 Linux: a run, not the source reading

A probe (`engines/duckdb/probes/avg_int.py`) ran on x86-64 Linux and macOS arm64 with DuckDB 2.0.0 and found `avg` of `BIGINT` gives the one division in doubles of the sum rounded to a double on both, for all 401 pairs chosen to separate it from an 80-bit division rounded again. The fact `duckdb-avg-int` records the result and that it disagrees with the source's `long double` reading
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

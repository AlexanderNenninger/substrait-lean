### DuckDB's integer mean depends on the plan's shape and the platform

DuckDB rewrites an ungrouped `avg` of integers to `SUM / COUNT`, which gives the model's value. A grouped or window `avg` keeps the native finalize, which on x86-64 Linux divides in 80 bits and rounds again, so its last bit can differ from the model's. The negative-sum cast of `HUGEINT` to `DOUBLE` rounds twice on every platform. The probes `avg_int.py` and `avg_int_shapes.py` count both, and the fact `duckdb-avg-int` records them
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

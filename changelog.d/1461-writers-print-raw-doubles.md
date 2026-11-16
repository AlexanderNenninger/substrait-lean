### The SQL writers print raw doubles

The DuckDB and Spark writers no longer add `+ 0.0` to float reads, scalar results and aggregates. The written plan gave `atan2((0.0 * -1.0) + 0.0, -1.0) = π` where the reference gives `-π`, and `1.0 / (x * -1.0)` gave `inf` for `-inf` under `semantics="duckdb"` (#1461). `round` and `ceil` print the proved template on DuckDB, and a stored `-0.0` now reaches the model: the plan's literal is the text `-0.0`, which the parser reads. DuckDB's own comparisons, groups, joins, window partitions and sort keys already read the zeros as one.

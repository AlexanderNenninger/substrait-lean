### The SQL lift reads `time_bucket`

DuckDB SQL with `time_bucket(width, ts[, origin])` lifts for a constant width of days or less (part of [#347](https://github.com/AlexanderNenninger/substrait-lean/issues/347)). The buckets count from DuckDB's default origin (2000-01-03), a constant timestamp origin, or the default plus a constant interval, and agree with DuckDB on negative and NULL timestamps. A width in months, a `DATE` argument and a computed origin are refused. A call spelled `date_bin`, which DuckDB 2.0.0 does not have, is refused.

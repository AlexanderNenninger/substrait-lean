### A double cast to a timestamp is read as seconds

Sverify reads Ibis's `x.cast("timestamp")` of a double as seconds since the
epoch, as DuckDB's `to_timestamp` does: the microseconds are `x * 1e6`
computed as a double and rounded half to even, so `2.5e-6` seconds is 2
microseconds ([duckdb-to-timestamp-double](engines/duckdb/facts/duckdb-to-timestamp-double.json)).
A value outside the timestamp range raises. `try_cast` and a cast to a
timestamp with a time zone stay refused
([#1922](https://github.com/AlexanderNenninger/substrait-lean/issues/1922)).

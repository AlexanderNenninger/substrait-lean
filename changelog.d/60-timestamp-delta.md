### Timestamp delta verifies

`ts.delta(other, unit)` for microsecond, millisecond, second, minute, hour and day counts the unit boundaries crossed ([D58](docs/decisions.md#d58-a-timestamps-delta-counts-the-unit-boundaries-crossed)), as DuckDB's `date_diff` does. It runs on DuckDB; other engines refuse it with "see #271". Week, month, quarter, year and nanosecond stay refused ([#60](https://github.com/AlexanderNenninger/substrait-lean/issues/60)).

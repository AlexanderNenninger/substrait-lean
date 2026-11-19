### A timestamp plus a column's interval verifies

`ts + col.as_interval("h")` (a count of days or less, from a column) is accepted for a timestamp, as it already was for a date, and runs on DuckDB. Other engines refuse it with "see #271" until their writers are lowered ([#60](https://github.com/AlexanderNenninger/substrait-lean/issues/60)).

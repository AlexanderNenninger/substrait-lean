### SQL lift: `MEDIAN` of a date or timestamp is refused

DuckDB interpolates the median of a date or timestamp (`2024-01-05 12:00:00` for the days 1 to 10) where the lift took the lower middle, a different value ([#2153](https://github.com/AlexanderNenninger/substrait-lean/issues/2153)). The lift now refuses it and names the rewrite: `quantile_disc(x, 0.5)` for the lower middle.

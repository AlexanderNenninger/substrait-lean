### `range` and `generate_series` as inputs, and built-in schema names

`FROM range(a, b[, step])`, `generate_series(…)` and `UNNEST(generate_series(…))` with constant integer, date or timestamp bounds are lifted as the rows they list (at most 10,000), so a date spine verifies (#321). A call qualified by its built-in schema (`main.lower(x)`, `pg_catalog.lower(x)`) reads as the bare function (#328).

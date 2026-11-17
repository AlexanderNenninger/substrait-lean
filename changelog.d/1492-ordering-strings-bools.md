### Strings and booleans can be ordered on DuckDB and Polars

A verified plan that compares strings or booleans with `<`, `BETWEEN`, `GREATEST` or `LEAST` now runs on
DuckDB and Polars, in the model's order: code point for strings, `FALSE < TRUE` for booleans. Before, `verify`
proved such a plan and both translators refused to run it (#1492).

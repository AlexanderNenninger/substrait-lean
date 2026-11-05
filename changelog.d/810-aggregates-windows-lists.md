### The SQL lift reads ordered aggregates, IGNORE NULLS, interval frames and list functions

Six constructs of the 1.0 coverage targets
([docs/coverage-targets.md](docs/coverage-targets.md)) now lift from DuckDB
SQL, verify and run on DuckDB; other engines refuse the new functions
([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)):

- `string_agg(x, sep ORDER BY …)` (`listagg`, `group_concat`), `list(x ORDER
  BY …)` (`array_agg`), `bool_and`, `bool_or`, and `first`/`last` with
  `ORDER BY`. DuckDB's `list`, `first` and `last` keep NULLs, and so does the
  plan ([#810](https://github.com/AlexanderNenninger/substrait-lean/issues/810)).
- `first_value(x IGNORE NULLS)` and `last_value(x IGNORE NULLS)`, the last
  observation carried forward, and `RANGE` frames with an `INTERVAL` of days
  or less over a timestamp or a date
  ([#811](https://github.com/AlexanderNenninger/substrait-lean/issues/811)).
- `len`, `array_length`, `list_contains` (`list_has`), `list_position`,
  `list_concat` and lists of computed elements (`[qty, id]`), modelled in Lean
  as DuckDB 2.0 computes them
  ([#812](https://github.com/AlexanderNenninger/substrait-lean/issues/812)).

DuckDB's SQL for `first` and `last` (the Ibis producer's `first()`, `last()`
and `arg_min`) is DuckDB's own `first(x ORDER BY …) FILTER (WHERE x IS NOT
NULL)`, without gathering each group's values into a list: 4 times faster on
5 million rows.

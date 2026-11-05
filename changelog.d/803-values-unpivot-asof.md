### The SQL lift reads VALUES, UNPIVOT and ASOF joins

Three relations of the 1.0 coverage targets
([docs/coverage-targets.md](docs/coverage-targets.md)) now lift from DuckDB
SQL and verify:

- `VALUES` in `FROM` and as a CTE, each column at the common type of its rows
  as DuckDB types it, named `col0`, `col1`, … without an alias
  ([#803](https://github.com/AlexanderNenninger/substrait-lean/issues/803)).
- `UNPIVOT [INCLUDE NULLS] (v FOR k IN (a, b AS 'x'))`, and the `UNNEST` of
  lists written out side by side (`unnest(['a', 'b']), unnest([a, b])`), as
  the `UNION ALL` they mean. Ibis's `pivot_longer` becomes the same union, so
  the catalogue's `dbt-unpivot-longer` verifies
  ([#804](https://github.com/AlexanderNenninger/substrait-lean/issues/804)).
- `ASOF [LEFT] JOIN` with `>=`, `>`, `<=` or `<`, written as
  `sverify.asof_join` writes it: a range join ranked by `ROW_NUMBER` per left
  row. Right rows that tie on the time leave the match to the engine, so the
  plan is reported as not deterministic
  ([#805](https://github.com/AlexanderNenninger/substrait-lean/issues/805)).

The lift no longer runs SQLGlot's type annotation, which nothing read, and
resolves each column type once: a lift takes a fifth less time.

Three fixes the replay of the new queries turned up:

- A RANGE frame's bounds overflow as in DuckDB: it computes `key ± offset`
  in an integer key's type and raises where a bound leaves it; the plan
  raises there too.
- A GROUP BY key that is the alias of a constant (`7 AS k … GROUPING SETS
  ((k), ())`) is that select column; the lift read the position `qualify`
  writes for it as the constant 1.
- `arg_min(x, y, n)` and `arg_max(x, y, n)`, which return lists of the `n`
  best, are refused; the lift dropped `n`.

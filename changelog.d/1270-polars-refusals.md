### Polars runs no Python: `log10`, `log2` natively, five operations refused

Polars's translation no longer calls Python per row or numpy per batch for
what Polars cannot compute exactly
([#1270](https://github.com/AlexanderNenninger/substrait-lean/issues/1270)).
`log10` and `log2` run as Polars's own `ln(x) / ln(b)`, within 2.1 ulp of
libm's, which the plan's float bound states (polars-ulp-libm). On Polars these
are refused with the reason and another engine to run them on: `ROUND(x, d)`
outside `0 ≤ d ≤ 22`, `%` of doubles, `levenshtein`, and `replace`, `LIKE` and
`ILIKE` with a pattern that is not a literal. DuckDB and Spark run them as
before.

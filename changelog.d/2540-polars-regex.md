### Polars runs `regexp_extract` and `regexp_replace`

Polars runs `regexp_extract` and `regexp_replace` (Ibis `re_extract`, `re_replace`) with a constant pattern, as DuckDB does: `''` where nothing matches, and the replacement's `\1` and `\\` as the reference reads them ([polars-regex](engines/polars/facts/polars-regex.json), [#2540](https://github.com/AlexanderNenninger/substrait-lean/issues/2540)).

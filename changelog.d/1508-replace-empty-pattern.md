### `replace` with an empty pattern returns the string unchanged

The model's `replace` put the replacement around every character, as Polars
does, and DuckDB returns the string unchanged, so a plan verified with an empty
constant pattern ran on Polars with another answer than the SQL gave on DuckDB.
The reference now gives DuckDB's value: `replace(s, '', r)` is `s`, and NULL for
a NULL `r`. Both frontends accept the empty pattern, and the SQL writers and the
Polars engine fold it to `s`, so every route gives the same answer
([#1508](https://github.com/AlexanderNenninger/substrait-lean/issues/1508)).

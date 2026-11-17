### `replace` with an empty pattern is refused under the reference and DuckDB's value under `semantics="duckdb"`

The model's `replace` puts the replacement around every character, as Polars
does, and DuckDB returns the string unchanged, so a plan verified with an empty
constant pattern ran on Polars with another answer than the SQL gave on DuckDB.
The SQL lift under `semantics="reference"` and the Ibis producer now refuse a
constant empty pattern, naming both values. `semantics="duckdb"` lifts
`replace(s, '', r)` to `s` (NULL for a NULL `r`), so every route gives DuckDB's
answer ([#1508](https://github.com/AlexanderNenninger/substrait-lean/issues/1508)).

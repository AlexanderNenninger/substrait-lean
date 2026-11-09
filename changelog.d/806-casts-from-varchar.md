### Casts from VARCHAR, and TRY_CAST of strings

`CAST(s AS BIGINT)` (and the narrower integers), `DOUBLE`, `BOOLEAN`, `DATE`
and `TIMESTAMP` of a string column lift and verify, with DuckDB's rules:
spaces around, signs, fractions and exponents, `inf` and `nan`, the boolean
words, ISO dates and times
([#806](https://github.com/AlexanderNenninger/substrait-lean/issues/806),
[`duckdb-cast-varchar`](engines/duckdb/facts/duckdb-cast-varchar.json)).
`CAST` raises on a string DuckDB rejects, which `verify` reports as a domain
error; `TRY_CAST` is NULL there, so `TRY_CAST(value AS DOUBLE)` reads
numbers stored as text with flags such as `12.3 p` or `:` for missing. The
Ibis API's `cast` and `try_cast` of a string verify too. They are black
boxes that run on DuckDB; other engines refuse them until #271. A string
to a DECIMAL is still refused (#27).

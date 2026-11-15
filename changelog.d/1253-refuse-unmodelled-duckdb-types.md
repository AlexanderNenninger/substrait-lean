### DuckDB UUID, ENUM, BIT and BIGNUM columns are refused with their exit

Arrow exports a DuckDB `UUID` as text, and DuckDB compares a string with a
`UUID` by casting the string, so a plan read as text proved the wrong rows
([#1253](https://github.com/AlexanderNenninger/substrait-lean/issues/1253)).
Sverify now refuses a column by the type DuckDB declares for it, whatever
Arrow exports it as (`UUID`, `ENUM`, `BIT`, `BIGNUM`, also inside a list,
struct or map), and the message names the exit: read it as text with
`CAST(col AS VARCHAR)` in the source query. Three engine facts record what
DuckDB does (`duckdb-uuid-text-order`, `duckdb-uuid-string-cast`,
`duckdb-enum-order`).

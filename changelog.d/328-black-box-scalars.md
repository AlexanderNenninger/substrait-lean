### More DuckDB scalars as black boxes

The SQL lift reads more of DuckDB's scalars
([#328](https://github.com/AlexanderNenninger/substrait-lean/issues/328)),
as rows of the black-box table: `printf` and `format` of a format and one
value, which may raise; `octet_length(encode(s))` and `strlen(s)`, the UTF-8
byte length, at least 0; `signbit` of a double; and `yearweek` of a date,
bounded by DuckDB's dates. Lean evaluates all but `printf` and `format`.
`weekday(d)` is now read as `dayofweek(d)`, exactly. `age` stays refused:
its INTERVAL is not in the model. The engine facts `duckdb-printf`,
`duckdb-signbit` and `duckdb-yearweek` record what DuckDB 2.0.0 does
([reference semantics](docs/reference-semantics.md#black-boxes)).

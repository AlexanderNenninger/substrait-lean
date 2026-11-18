### `CAST(round(x) AS BIGINT)` of a double lifts from DuckDB SQL

Under `semantics="duckdb"`, `sv.sql` now lifts `CAST(round(x) AS BIGINT)`,
and the same with `floor` and `ceil`, where `x` is a `DOUBLE`. Sverify proves
the lifted plan computes what DuckDB does: the rounded value is integral, so
DuckDB's half-to-even cast and the model's truncating cast agree, and NaN,
±∞ and values past 2⁶³ raise in both. A bare `CAST(x AS BIGINT)` of a double
and casts to narrower integer types stay refused
([#1655](https://github.com/AlexanderNenninger/substrait-lean/issues/1655)).

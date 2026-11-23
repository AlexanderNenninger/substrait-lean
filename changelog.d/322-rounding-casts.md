### The SQL lift reads `CAST(double AS BIGINT)` as DuckDB's rounding

`sv.verify` of DuckDB SQL lifts `CAST(x AS BIGINT)` of a double, under both `semantics`, as the cast of the half-to-even round, which is what DuckDB computes ([#322](https://github.com/AlexanderNenninger/substrait-lean/issues/322), D55). A plan's `round(x, rounding: TIE_TO_EVEN)` at zero digits is read and written on DuckDB, Polars and Spark. Casts of a double to narrower integers stay refused, with the spelling that lifts.

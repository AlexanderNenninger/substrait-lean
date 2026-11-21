### Six more DuckDB rows are proved

DuckDB's `division_type`, `round`'s rounding, NaN equality, `substring`'s
negative start, `LIKE`'s case sensitivity and string positions are now
proved by the generated lowering (`Lowering.duckdb_exact`), so a plan that
reads them no longer lists them as tested rows
([#1985](https://github.com/AlexanderNenninger/substrait-lean/issues/1985)).
DuckDB's integer powers are named as a shim, written as checked products.

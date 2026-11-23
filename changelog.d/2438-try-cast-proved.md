### `try_cast` of a double to an integer is proved again on every engine

Each engine's table now states its double or decimal to integer cast
(`float_to_int` at `cast.num`, ruling 273): Polars and Spark truncate natively,
and DuckDB's cast rounds, so its lowering writes `trunc` first, a shim. The
route of `try_cast` goes back from tested to proved on DuckDB, Polars and Spark
([#2438](https://github.com/AlexanderNenninger/substrait-lean/issues/2438)).

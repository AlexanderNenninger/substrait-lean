### The DuckDB and Spark writers print a zero class's canonical value for MIN, MAX and keys

Where the engine's pick among equal zeros depends on row order or partitioning (`MIN` and `MAX` of doubles on DuckDB and Spark, and a double group key or `DISTINCT` row on DuckDB), the written plan adds `+ 0.0`, so a rerun gives the same sign and the plan stays inside the reference's allowed values (D31). `sverify.testing.canonical` reads `-0.0` as `0.0` and says so in its docstring (#1461).

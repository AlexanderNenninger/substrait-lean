### A plan that states `division_type: FLOOR` runs on every SQL engine

The SQL writer computes integer `//` and `%` with `division_type: FLOOR`
(the plans `semantics="polars"` writes) from truncating operations, as the
checker reads them (`Expr.floorDivOf`, `Expr.floorModOf`). DuckDB, Spark and
Snowflake no longer refuse such a plan before it runs: Spark's route proves
it again under `semantics="spark"` and runs it, and the written plan runs on
DuckDB with Polars's values. The route to DuckDB stays refused by the
transfer check, since the proof under Polars's profile does not carry over
to DuckDB's ([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

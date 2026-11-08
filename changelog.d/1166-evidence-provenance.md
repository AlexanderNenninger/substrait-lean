### Every tested engine row names the issue tracking its proof

An engine profile's observation rows that rest on tests or probes, not on a
Lean theorem, now name the issue that tracks their proof, and the checker
refuses a profile with a row that names none (`EngineProfile.tracked`,
#1131, #1166). `--options` and `--realizability` print each row's `issue`
and the engine `version` its facts were checked at, beside its `facts` and
`theorem`. Three rows that a theorem already covers are marked proved:
DuckDB's `MIN % -1` (`Lowering.duckdb_exact`), DuckDB's one zero after
`Dialect.canon` (`Spark.one_zero`, the same `x + 0.0`), and the sort a
clustered key gets on Polars and Spark (`Rel.polars_sound`,
`Rel.spark_sound`).

### Every tested engine row names the issue tracking its proof

An engine profile's observation rows that rest on tests or probes, not on a
Lean theorem, now name the issue that tracks their proof, and the checker
refuses a profile with a row that names none (`EngineProfile.tracked`,
#1131, #1166). `--options` and `--realizability` print each row's `issue`
and the engine `version` its facts were checked at, beside its `facts` and
`theorem`. DuckDB's `MIN % -1` row, which the generated lowering entry
covers, is marked proved (`Lowering.duckdb_exact`).

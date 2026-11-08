### A verified contract holds on each engine's model, in Lean

- `Engine.contract_sound` proves that a contract verified under the reference
  holds on the rows the models of DuckDB, Polars, Spark and the reference
  compute for the translated plan, unless it raises
  ([#900](https://github.com/AlexanderNenninger/substrait-lean/issues/900)).
  Each engine's bridge, `Engine.Sound`, is a theorem (`SubstraitLean/EngineSound.lean`).
  The engine's actual output rests on the trusted claim `Engine.Runs` and the
  transfer check (`Engine.contract_sound_runs`). The check fails today at
  `sum_order`, `stat_algo`, `quantile_interp` and `zero_sign` on every engine,
  `null_order` without a preference on Polars and Spark, and integer overflow
  on Polars; the tolerance form for those is #900's PR 3.

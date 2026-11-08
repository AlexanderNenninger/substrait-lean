### A verified contract holds on each engine's run, in Lean

- `Engine.contract_sound` proves that a contract verified under the reference
  holds on the rows DuckDB, Polars, Spark and the reference compute for the
  plan, unless the translated plan raises
  ([#900](https://github.com/AlexanderNenninger/substrait-lean/issues/900)).
  Each engine's bridge, `Engine.Sound`, is a theorem (`SubstraitLean/EngineSound.lean`).
  For the engine's actual result, `Engine.contract_sound_runs` needs the
  engine's choices to be the reference's at the options the plan reads; where
  they differ (double `SUM`, statistics, quantiles, grouping by doubles) the
  tolerance form follows.

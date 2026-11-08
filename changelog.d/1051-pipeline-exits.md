### Refresh, export, sharding and sverify-dbt refusals name their exit

- `NotIncrementalError` from a standalone view names the way out: a view in
  a `Pipeline` (a node built with `.pipe`) is recomputed and diffed instead.
  `AuditError` says what to check and where to report a mismatch; a
  precondition on a view says to state it in the `ensures` of the transform
  that builds it; foreign keys in views name #869
  ([#1051](https://github.com/AlexanderNenninger/substrait-lean/issues/1051)).
- `ExportError` for a relation, expression or function `to_substrait` cannot
  write names `report.to_sql(dialect)`
  ([#1053](https://github.com/AlexanderNenninger/substrait-lean/issues/1053)).
- `NotShardable` for a `SUM` or `AVG` of doubles names
  `run_sharded(reproducible=sv.equivalent(floats="plan"))` in place of the
  deprecated `float_order="any"`
  ([#1054](https://github.com/AlexanderNenninger/substrait-lean/issues/1054)).
- sverify-dbt says that dbt still runs a test it does not map, a foreign key
  of a result or a Python model's tests, how to map it
  (`dbt_utils.expression_is_true`, `{{ ref() }}`), and keeps sverify's own
  exit in a refusal; before, it kept only the message's first line
  ([#1055](https://github.com/AlexanderNenninger/substrait-lean/issues/1055)).
- `sv.asof_join`'s docstring no longer claims operators Lean verifies: the
  join has no theorem of its own and is proved as any plan, by
  `contract_sound_all` and `Rel.keys_sound_all`, which `docs/proofs.md` now
  lists for it ([#1052](https://github.com/AlexanderNenninger/substrait-lean/issues/1052)).

### Sharded integer AVG

`--shard` and `sverify.engines.run_sharded` split an integer `AVG` (Substrait's
`avg` of `i64` with an `i64` result) across shards: each shard computes a `SUM`
and a `COUNT`, the combining plan adds them up and divides, truncating toward
zero. Lean proves it once for algebraic aggregates, a final expression over
distributive partials (`Rel.eval_algebraic` in `SubstraitLean/Partition.lean`),
when the plan's column types make the argument an integer. `AVG` with a double
result is still refused with `float_order="exact"` ([#245](https://github.com/AlexanderNenninger/substrait-lean/issues/245)).

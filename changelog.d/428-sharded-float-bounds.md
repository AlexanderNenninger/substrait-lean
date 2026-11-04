### Proved error bounds for sharded double `SUM` and `AVG`

`--shard` and `sverify.engines.run_sharded` with `float_order="any"` now split
`SUM` and `AVG` of doubles with a proved bound on how far each result is from
Lean's one-pass sum. Each shard also reports `SUM(|x|)`, `COUNT(x)` and
`MAX(|x|)` per split double, `--shard`'s output says which columns carry the
bound (`float_bounds`, `Split.float_bounds`), and `run_sharded(...,
tolerance=True)` returns a `Sharded` with τ per row and column.
`sverify.partition.apriori_tolerance` gives the bound before running, from a
row cap and a bound on the values. The bounds are proved in
`float-bounds/FloatBounds/Shard.lean` and linked to the split plan by
`floatSplit_sum` and `floatSplit_avg` in `SubstraitLean/Partition.lean`
([#428](https://github.com/AlexanderNenninger/substrait-lean/issues/428)).

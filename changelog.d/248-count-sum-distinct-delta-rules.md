### COUNT, SUM and DISTINCT are maintained from changes

A node that ends in an aggregate of `COUNT` and integer `SUM` per group, or
in `DISTINCT`, is now maintained from the changes to its input when the
input has delta rules. It keeps a count and a sum per group beside its rows
and adds each batch's change to them, so a refresh no longer reads the input
of the groups a batch touches, and `status()` reports the node as
maintained. Lean proves the result equal to a full recompute, groups that
appear and disappear included (`LinearAgg.aggregate_maintained` and
`LinearAgg.distinct_maintained`). An integer `SUM` that leaves 64 bits still
raises, as on a full recompute. This is the first stage of
[#248](https://github.com/AlexanderNenninger/substrait-lean/issues/248).

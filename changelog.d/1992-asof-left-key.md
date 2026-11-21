### A left key survives `sv.asof_join`

A key of the left table that `requires` states is now proved a key of
`sv.asof_join`'s output, for `how="left"` and `how="inner"`: `unique(order_id)`
on the facts gives `unique(order_id)` after the join
([#1992](https://github.com/AlexanderNenninger/substrait-lean/issues/1992)).
The key analysis keeps a dependency through a projection's copies of the
columns it depends on, which helps any plan that renames or reorders columns
above a join.

### Incremental `SUM` and `AVG` of doubles, exactly

A view that ends in `SUM` or `AVG` of `DOUBLE` per group is now maintained
from an exact state (the count, the exact sum and the NaN and infinity
counts of each group) instead of recomputing the groups a batch touches. Its
value is the correctly rounded sum of the current rows after any sequence of
inserts and deletes, with no drift, which Lean proves
(`LinearAgg.fsum_no_drift`, #918). `LinearAgg.aggregate_maintained` now
covers any measure with a linear state, `COUNT` and `SUM` among them. A
`SUM` of `FLOAT`, or of doubles beside a `MIN` or `MAX`, still recomputes
the touched groups. A prototype on DuckDB (`python -m sverify_dev.ivm_float_sum`)
measures the drift a running double sum accumulates instead.

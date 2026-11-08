### Incremental `VAR`, `STDDEV`, `COVAR` and `CORR` of doubles, exactly

A view that ends in `VAR`, `STDDEV`, `COVAR` or `CORR` of `DOUBLE` per group
is now maintained from its exact moments (the count, `Σx`, `Σx²`, and for a
pair `Σy`, `Σxy`, `Σy²`) instead of recomputing the groups a batch touches.
Its value is D30's, the exact moments rounded once, after any sequence of
inserts and deletes, which Lean proves (`LinearAgg.no_drift`,
`varState_sound`, `covState_sound`, `corrState_sound`, #918).

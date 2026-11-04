### Polars runs the reference natively, with named shims

The Polars engine now runs integer `+`, `-`, `*`, division and remainder, and
`SUM` and `AVG` of a group as Polars's own operations. Where Polars 2.1.0
gives another value than the reference on inputs the reference does not raise
on, a named shim (`sverify._polars_shims.SHIMS`) gives the reference's:
truncating division and remainder, `ROUND`'s halves away from zero, `NULL` for
an empty `SUM`, the integer `AVG` in its declared type, one zero, each sort
key's NULL placement and stable ties. Each shim names the Polars fact it rests
on ([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

A double `SUM` or `AVG` now adds in Polars's own order, which the reference
allows (`sum_order = ANY`), so its last bits may differ from `Rel.eval`'s. A
sort key without a direction sorts ascending with NULLs last. `guards=` of
`run` and `to_lazy` also takes the issues to check by name, such as
`{"SUM overflow", "overflow to infinity"}` for the preconditions a report
assumes ([#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575)).

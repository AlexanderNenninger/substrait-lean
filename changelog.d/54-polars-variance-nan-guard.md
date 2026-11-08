### Polars's variances keep a NaN

On Polars, a `VAR_*` or `STDDEV_*` of a group with a NaN returns NaN, as the
reference does. Polars's streaming `group_by` over a one-row frame gives 0
for a NaN (polars-var-pop-one-nan); sverify's plans did not take that path,
and now return NaN whichever path Polars takes (`_polars_shims.nan_through`).
The variance is aggregated once and clamped when it is read, so a plan
computes `var` or `std` once per measure, where it computed it nine times.

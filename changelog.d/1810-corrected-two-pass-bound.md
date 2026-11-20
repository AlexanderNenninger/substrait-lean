### The corrected two-pass bound is proved

`FloatBounds.StdModel.corrTwoPass_error` bounds the textbook formula
`Σ d² − (Σ d)² / n` applied to doubles shifted by any constant, which is how
sverify writes Snowflake's `VAR_*` (values minus their group's mean), with
both sums added in any order an engine may use
([#1810](https://github.com/AlexanderNenninger/substrait-lean/issues/1810)).
For the group's mean the bound is `(2n + 9) u S` to first order.

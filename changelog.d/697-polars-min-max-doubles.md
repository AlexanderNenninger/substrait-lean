### `MIN` and `MAX` of doubles run on Polars

`MIN` and `MAX` of doubles, as aggregates and as window functions, run on
Polars by `route="auto"` ([#697](https://github.com/AlexanderNenninger/substrait-lean/issues/697)).
Polars's `min` and `max` skip NaN and may keep either zero
([polars-min-max-nan](characterization/polars/facts/polars-min-max-nan.json),
[polars-min-max-zero](characterization/polars/facts/polars-min-max-zero.json)):
the translation gives `MAX` of a group with a NaN as NaN, the greatest double,
and reads both results with one zero. The shim `max_nan_greatest` and
`Polars.min_ignore_nan` are proved in `SubstraitLean/PolarsShims.lean`, and
the route's class is `shim`.

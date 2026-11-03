### Contracts on rollups: `MIN`, `MAX` and `AVG` of a group

A rollup's natural contract is now proved before any data runs: averages
within the inputs' range, `MAX ≥ AVG`, and no NULL measures.

- `MIN` and `MAX` of doubles are accepted (#371). DuckDB orders doubles as
  the reference does, `-∞ < … < +∞ < NaN`; Polars and DataFusion refuse them
  until #271.
- `MIN`, `MAX` and `AVG` of a column that is never NULL, over a group
  without a filter, are never NULL (#372).
- Measures of the same values on one group are related: `MIN ≤ AVG ≤ MAX`
  and `MIN ≤ MAX`, also for the mean of integers, which is a double (#372).
- `AVG` of integers, decimals and doubles lies within its values' bounds
  (#237). The `AVG` of doubles is now kept between the smallest and largest
  value: IEEE's rounding can step past them (the mean of three `0.1` is
  `0.10000000000000002`), and the reference and the engines running its plan
  return `0.1` there.
- A conversion of integers to doubles keeps their bounds: `CAST(x AS DOUBLE)`
  of `x` in `[0, 1000]` is in `[0.0, 1000.0]`.

Arithmetic on doubles still gives "some double", so `AVG(x) / 10` has no
bound yet.

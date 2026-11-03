### Contracts on rollups: `MIN`, `MAX` and `AVG` of a group

More of a rollup's contract is proved before any data runs.

- `MIN` and `MAX` of doubles are accepted (#371). DuckDB orders doubles as
  the reference does, `-∞ < … < +∞ < NaN`; Polars and DataFusion refuse them
  until #271.
- `MIN`, `MAX`, `AVG` and `SUM` of a column that is never NULL, over a group
  without a filter, are never NULL (#372).
- `MIN ≤ MAX` for measures of the same values on one group, and an integer
  `AVG` with an integer result lies between them (#372).
- A decimal `AVG` and an integer `AVG` with an integer result lie within their
  values' bounds (#237). TPC-H Q17's `0.2 * avg_qty` is now proved not to
  overflow.
- A conversion of integers to doubles keeps their bounds: `CAST(x AS DOUBLE)`
  of `x` in `[0, 1000]` is in `[0.0, 1000.0]`.

An `AVG` of doubles, including the mean of integers as a double, rounds and
can step past its values (the mean of three `0.1` is `0.10000000000000002`),
so it gets no bound from its inputs here. Error bounds for it come with #85.

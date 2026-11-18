### `suggested_requires` states the bound a hint names

A refusal that proves once a bound is stated now puts that bound in
`report.suggested_requires`: `_.total.between(-1e300, 1e300)` for a `SUM` or
`AVG` of a double (also behind a join or a CTE) and the integer bounds of a
`LAG` overflow. `requires=report.suggested_requires` proves them
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

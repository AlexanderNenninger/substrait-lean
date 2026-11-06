### Decimals on Spark

Decimal plans run on Spark (#27,
[#739](https://github.com/AlexanderNenninger/substrait-lean/issues/739)):
`+`, `-`, `×`, comparisons, casts, `SUM`, `MIN` and `MAX`, at the reference's
types and rounding.

- Spark's `-x` and `abs` round a decimal past 34 significant digits
  ([SP-1](upstream/bugs/SP-1.json)). The writer negates as `0 - x` there,
  exact up to 37 digits, or 38 at a scale of 6 or less, and refuses a
  `DECIMAL(38, s)` with `s > 6`; `Spark.decimal_negate_sub` proves the choice.
- A sum or product whose type would pass 38 digits at a scale above 6 is
  refused, since Spark would cut its scale. A double cast to a decimal past
  18 digits and an `AVG` of decimals are refused too, each naming the
  construct.
- `sverify.testing.decimal_literal` keeps every digit of a decimal wider
  than 28 digits; it used to round them.
- A routed run on Spark sends a table to the session once: a later run over
  the same table keeps its view.

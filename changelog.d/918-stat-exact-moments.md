### `VAR`, `STDDEV`, `COVAR` and `CORR` are the exact moments rounded once (D30)

The reference's statistical aggregates of doubles are now one value each: the
exact moments of the values (`n`, `Σx`, `Σx²`, `Σxy`) rounded once
([#918](https://github.com/AlexanderNenninger/substrait-lean/issues/918)). They
no longer leave the engine a choice, so contracts over them hold of every
result the reference allows, and three axioms (`varOf_props`, `covOf_props`,
`corrOf_props`) are retired. Engines keep their own algorithms, within the
plan's bound: their rows are `approx`, `Report.epsilon` reports a bound for
variance and deviation columns, and the written SQL clamps a variance at `0`
and a correlation to `[-1, 1]`. Results can differ by an ulp from 0.7's.

### Spark's profile is Spark's own

- Spark's profile states what Spark 4.3.0 computes under ANSI mode, from its
  [facts](../engines/spark/facts/): NaN where an operation creates one, NULL
  for a logarithm of `x ≤ 0`, no IEEE division, and the shift counts modulo
  64. It was the reference's
  ([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)).
- Until the checker reports under it
  ([#1288](https://github.com/AlexanderNenninger/substrait-lean/issues/1288)),
  `verify(semantics="spark")` gives the reference's report, with doubles that
  overflow allowed to be ±inf as before. `report.semantics` is `"reference"`,
  a `ProfilePendingWarning` says so, and the plan reaches Spark through its
  translation (route `translated`, before `native`).

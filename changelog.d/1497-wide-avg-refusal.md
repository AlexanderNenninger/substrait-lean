### The refusal of a wide decimal `AVG` names the way through

`AVG` of a decimal over 34 digits stays refused, since its `DECIMAL(p + 4, s + 4)` result must fit 38 digits ([#1497](https://github.com/AlexanderNenninger/substrait-lean/issues/1497)). The message now says to cast the argument to `DECIMAL(34, s)` or narrower first, which verifies (the cast's overflow becomes an inferred bound) and runs to the exact mean, and `docs/reference-semantics.md` states both limits, precision and scale.

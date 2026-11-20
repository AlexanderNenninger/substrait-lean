### Spark runs the logarithms of doubles

Spark now runs `ln`, `log10`, `log2` and `log(b, x)` of doubles natively ([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)).
Its values are Java's, within 1 ulp of the exact result by its source
(spark-ulp-libm), and the plan's float bound adds each function's distance
from libm's value per call. `exp`, `sin`, `cos`, `tan`, `asin`, `acos` and `atan` have their bounds
and writer too, but `sverify.verify` still refuses them on Spark, as it does `sqrt`: their group
reads `pow_one_inf`, which Spark refuses. `sin`, `cos` and `tan` are bounded up to 2²⁰. `power` and
`atan2` stay refused. The bounds of Polars's `log10`, `log2` and `log(b, x)` and DuckDB's
`log(b, x)` are restated as the sum of both distances, so they are wider.

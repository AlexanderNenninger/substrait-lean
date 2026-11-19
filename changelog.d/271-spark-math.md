### Spark runs `exp`, `ln`, the logarithms and the trigonometric functions

Spark now runs `exp`, `ln`, `log10`, `log2`, `log(b, x)`, `sin`, `cos`, `tan`, `asin`, `acos`
and `atan` of doubles natively ([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)).
Its values are Java's, within 1 ulp of the exact result by its source
(spark-ulp-libm), and the plan's float bound adds each function's distance
from libm's value per call. `sin`, `cos` and `tan` have a bound for arguments up to 2²⁰. `power` and
`atan2` stay refused. The bounds of Polars's `log10`, `log2` and `log(b, x)` and DuckDB's
`log(b, x)` are restated as the sum of both distances, so they are wider.

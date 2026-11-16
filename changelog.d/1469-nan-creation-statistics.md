### A variance, covariance or correlation of an infinity allows any value under an engine's semantics

A variance, standard deviation, covariance or correlation of a `+∞` or `-∞` is a NaN made by the aggregate, so `nan_creation` governs it (as for a double `SUM` or `AVG`). Under `semantics="polars"` and `semantics="spark"` the checker no longer bounds such a result by the statistics' properties, and any value is allowed there; the reference still raises, so a verified plan under the reference is unchanged ([#1469](https://github.com/AlexanderNenninger/substrait-lean/pull/1469)).

### Exact double aggregates fold in Arrow, whatever the values

A maintained `SUM`, `AVG`, `VAR`, `STDDEV`, `COVAR` or `CORR` of doubles used to add rows with a NaN, an infinity or a weight of 256 or more to its exact state one at a time in Python. Arrow now sums them per group like every other row, so a batch full of NaNs or of rows repeated many times folds about twice as fast, and the result is the same exact state ([#1447](https://github.com/AlexanderNenninger/substrait-lean/issues/1447)).

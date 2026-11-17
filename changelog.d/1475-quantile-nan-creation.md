### QUANTILE_CONT of infinities reads nan_creation; Polars and Spark interpolate as LINEAR_DIFF

`quantile_cont` and `median` between a `-∞` and a `+∞` neighbour are a NaN made by the aggregate: `nan_creation` governs them, and the reference raises. Polars and Spark compute `lo + (hi − lo)·w`, which is NaN with a `-∞` lower neighbour and any greater upper one; their `quantile_interp` behaviour is now `LINEAR_DIFF` (between the neighbours, or NaN), and their quantile rows are refused under the reference route ([#1475](https://github.com/AlexanderNenninger/substrait-lean/pull/1475)).

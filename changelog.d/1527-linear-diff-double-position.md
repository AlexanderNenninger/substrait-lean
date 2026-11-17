### Polars and Spark quantiles: LINEAR_DIFF reads the engine's double position

Polars and Spark compute the quantile position `(n − 1)·q` in doubles, so at some positions that are whole in exact arithmetic they interpolate toward the next value. Their `quantile_interp` behaviour `LINEAR_DIFF` now takes the neighbours of that double position, so it states what the two engines compute. The reference stays at the exact position ([#1527](https://github.com/AlexanderNenninger/substrait-lean/pull/1527)).

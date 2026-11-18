### `COUNT(DISTINCT x)` is written natively

The written SQL counts the distinct values of a non-double column with the
engine's own `COUNT(DISTINCT x)`, not a `ROW_NUMBER` over the group and the
value ([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).
On 5 million rows it takes 0.08 s, down from 0.30 s.

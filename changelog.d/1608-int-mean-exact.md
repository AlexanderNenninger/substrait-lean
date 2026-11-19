### A mean of a bounded integer column is exact

A double `SUM` or `AVG` of an integer column whose values are at most `M` in
magnitude, over at most `N` rows with `N · max(M, 1) ≤ 2^52`, is now exact on
every engine: every summation order adds such integers exactly, and a mean
divides once, as the reference does. Its column reports no tolerance, so a
threshold on it, such as `qty > (SELECT AVG(qty) FROM orders)` with a bound on
`qty` and `sv.max_rows`, lowers instead of being refused ([#1608]). D35 is
amended for the summation orders Sverify takes on trust (DuckDB's constant
runs, Polars's in-memory Kahan sum), with each engine's tests as evidence.

[#1608]: https://github.com/AlexanderNenninger/substrait-lean/issues/1608

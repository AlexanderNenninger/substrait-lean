### A row cap bounds a `COUNT`

With `sv.max_rows(n)` on its input, a `COUNT` is proved to be at most `n`, as an
integer `SUM` already was. A query that multiplies or adds a count now proves
its result fits `BIGINT` from a bound on the column and a row cap. This covers
the exact exit of a threshold computed from the data, `x * COUNT(y) > SUM(y)`,
which the refusal of `x > (SELECT AVG(y) …)` names ([#1608]). Without a cap the
product still has an `overflow` error.

[#1608]: https://github.com/AlexanderNenninger/substrait-lean/issues/1608

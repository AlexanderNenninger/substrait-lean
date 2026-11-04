### `sv.rows_per` bounds the rows per key, and row caps bound exact sums

`sv.rows_per(["customer"], at_most=n)` in `requires` states that at most `n`
rows of an input agree on the columns. It is checked on the data like
`unique`. Lean carries the bounds through filters, sorts, `DISTINCT`,
projections, unions and joins on a key, and an aggregate grouping by the
columns has groups of at most `n` rows. So an integer or decimal `SUM` of
values in `[-m, m]` per group is proved to fit when `n · m` does, without a
cap on the whole table
([#219](https://github.com/AlexanderNenninger/substrait-lean/issues/219)).
`Report.relations` lists the bounds on each relation's rows.

A row cap (`sv.max_rows`) now also bounds the value of an exact `SUM`, so
decimal arithmetic on a sum, such as TPC-H q11's `SUM(…) * 0.0001`, can be
proved to fit
([#470](https://github.com/AlexanderNenninger/substrait-lean/issues/470)).

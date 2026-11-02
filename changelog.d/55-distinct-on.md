### `distinct(on=)`, and `first()`/`last()` without an order

Ibis's `distinct(on=…)` and `first()`/`last()` without `order_by` (DuckDB's
`FIRST`/`LAST` with no `ORDER BY`) are now verified rather than refused
(#55). They take any row's value, so the report says the result is not
`deterministic`, and proves nothing about it, unless the grouping (`on`)
columns form a key. Each column is chosen on its own: `distinct(on="name")`
may keep `a` from one row and `b` from another, so a fact about every input
row, such as `a <= b`, need not hold of the result. They run on DuckDB for
now; the other engines refuse them until #271.

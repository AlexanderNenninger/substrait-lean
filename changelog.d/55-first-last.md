### `first()` and `last()` with an order

Ibis's `first(order_by=…)` and `last(order_by=…)` (DuckDB's `FIRST(x ORDER
BY …)`) are verified: the first or last non-NULL value in that order, NULL
without one (#55). Without `order_by` they are any row's value and stay
refused. Where rows tie in the order, the report says the result is not
`deterministic`, unless the grouping and order columns form a key. They run
on DuckDB for now; the other engines refuse them until #271.

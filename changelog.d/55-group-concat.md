### `group_concat()` with an order

Ibis's `group_concat(sep, order_by=…)` (DuckDB's `STRING_AGG(x, sep ORDER
BY …)`) is verified: the non-NULL strings in that order, joined by a constant
separator, and NULL without values (#55). Without `order_by` the order is
the engine's, so it stays refused. As for `first()` and `last()`, rows that
tie in the order make the report not `deterministic` unless the grouping and
order columns form a key. It runs on DuckDB for now; the other engines refuse
it until #271.

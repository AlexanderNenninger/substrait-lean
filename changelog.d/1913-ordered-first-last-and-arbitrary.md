### `first(order_by=)`, `last(order_by=)` as windows and `arbitrary()`

`first(order_by=)` and `last(order_by=)` over a window ([#1913](https://github.com/AlexanderNenninger/substrait-lean/issues/1913)) are read as `FIRST_VALUE` / `LAST_VALUE` over the whole partition in that order, as Ibis writes them. `arbitrary()` ([#1920](https://github.com/AlexanderNenninger/substrait-lean/issues/1920)) is read as `first()` without an order: a non-NULL value of the group, proved as membership, reported as the engine's choice unless the group is a key.

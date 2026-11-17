### `asof_join` keeps every left row

`sv.asof_join` dropped all but one of the left rows that share their `by` and
`on` values (and the rows with a NULL `on`), and the plan was proved. The
ranking is now per left row, numbered first, so each row keeps its match and
the output has one row per left row. `unique(by, on)` of the output is no
longer proved: it was true only because rows were dropped. The `key=` parameter,
which named the columns that identified left rows, is gone
([#1517](https://github.com/AlexanderNenninger/substrait-lean/issues/1517)).

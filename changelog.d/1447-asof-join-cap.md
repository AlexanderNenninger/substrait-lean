### `asof_join` refuses a join that would compare more than 10⁸ pairs of rows

`sv.asof_join` is a range join, so the pairs of rows it compares (each left
row with every right row of its `by` group) are quadratic in the rows
([#1447](https://github.com/AlexanderNenninger/substrait-lean/issues/1447)).
Where both tables are held by a `sverify.connect()` connection, it now counts
them and raises `UnsupportedError` above `max_pairs` (default 10⁸, which keeps
DuckDB's join under about 7 seconds), naming the exits: `by` columns, fewer
rows, or a larger cap (`max_pairs=None` for none).

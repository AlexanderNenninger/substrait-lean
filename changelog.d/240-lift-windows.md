### The SQL lift reads window functions

The SQL lift now reads window functions (#240):
- **Ranking:** `row_number`, `rank`, `dense_rank`, `percent_rank`, `cume_dist` and `ntile`.
- **Values:** `lag` and `lead` (a constant offset, and a default), `first_value`, `last_value` and `nth_value`.
- **Aggregates:** `sum`, `avg`, `count`, `min` and `max` over a window, including windows over a query's aggregates (`rank() OVER (ORDER BY sum(x))`).
- **Frames:** `ROWS` and `RANGE` frames with integer offsets, and DuckDB's default frame: to the current row and its peers with an `ORDER BY`, the whole partition without.

`ntile` is DuckDB's, the SQL standard's buckets: 6 rows in 4 tiles are 1 1 2 2 3 4. The lift writes it from `row_number` and `count`, because the model's own `ntile` is DataFusion's. Named windows (`WINDOW w AS …`), `GROUPS` frames, `EXCLUDE`, `IGNORE NULLS` and `DISTINCT` in a window are refused.

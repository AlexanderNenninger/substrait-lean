### TIME constants, substring ranges and retention under a projection

- `TIME '13:45:21'`, `CAST('…' AS TIME)` and a string compared with a `TIME`
  column now lift to a TIME literal, so queries that compare a `TIME` column
  with a constant verify. Constants DuckDB raises on, and `24:00:00`, are
  refused (#386).
- `substring` with a constant offset outside [-2³², 2³²) or a constant
  length of 2³² or more is refused: DuckDB raises there, and the model has
  no such error yet (#336).
- Retention engages for an aggregate under a filter or a projection, such as
  a per-mille-to-percent `select` after the `aggregate` (#394).

### The SQL lift reads a qualified call as DuckDB does

The lift reads `main.lower(x)` and `system.main.lower(x)` as `lower(x)`, as
DuckDB does, and refuses `pg_catalog.lower(x)`, `memory.main.lower(x)` and
`system.pg_catalog.lower(x)`, which DuckDB refuses with a binder error. `len`
and `substr` lift as `length` and `substring`, tested against DuckDB (#328).

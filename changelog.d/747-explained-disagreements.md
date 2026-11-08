### The SQL lift refuses string casts DuckDB rejects

- `'_12.12'::DECIMAL(4,2)` and `'1e-9999999999'::DECIMAL` are refused by the
  SQL lift. DuckDB raises on them, and the lift used to fold them to `12.12`
  and `0.000` (#747).

### `verify` holds schemas, not a DuckDB connection

`sv.verify` builds its plans over unbound Ibis tables and the lift reads the input schemas directly, so a verification no longer starts a DuckDB database and uses about 30 % less memory. Results are unchanged. This is the first step of moving DuckDB to an extra (#1485, 16).

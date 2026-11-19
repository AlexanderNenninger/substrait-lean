### Every module imports without DuckDB, and `verify` runs without it

Importing any `sverify` or `sverify_duckdb` module no longer imports `duckdb`, and `sv.verify` proves a plan, from Ibis or from SQL, in an environment that has none. What runs on DuckDB (`sv.connect("duckdb")`, table reads and sinks) raises `ImportError: this needs DuckDB: pip install 'sverify[duckdb]'`. The DuckDB engine counts as installed for running plans only where `duckdb` is. DuckDB is still a dependency of `sverify`; moving it to an extra follows (#1485, 16).

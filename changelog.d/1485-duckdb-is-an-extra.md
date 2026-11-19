### DuckDB is an extra: `pip install 'sverify[duckdb]'`

`pip install sverify` now installs no engine and no `duckdb`: `sv.verify`, the SQL dialects and `report.to_sql` work, and everything that runs plans or holds tables raises `ImportError: this needs DuckDB: pip install 'sverify[duckdb]'` or names the extra of the engine. That makes sverify installable beside `soda-core-duckdb` (`duckdb<1.1`). Add the extra where you relied on the implicit DuckDB: `sverify[duckdb]`, or `sverify[all]`, which now includes it. `sverify-dbt` brings DuckDB itself (#1485, 16; #1288).

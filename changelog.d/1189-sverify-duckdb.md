### DuckDB is a package of its own: sverify-duckdb

sverify's DuckDB engine moves into the distribution `sverify-duckdb`
(`engines/duckdb/`, package `sverify_duckdb`), released with sverify at its
version ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
`pip install sverify` installs it with DuckDB, as before, and it registers its
`ProfilePlugin` in the entry-point group `sverify.profiles` as a package from
outside does. DuckDB's facts move to `engines/duckdb/facts/`, the replay of
its sqllogictests, the fuzz findings and the probes to `engines/duckdb/replay/`.

The DuckDB dialect module `sverify.sql.duckdb` is now `sverify_duckdb.dialect`
(`DUCKDB`); `"duckdb"` still names the default dialect.

For now `sverify` itself depends on `sverify-duckdb[run]` and on DuckDB: the
table store behind `sv.connect()` runs on DuckDB (`sverify_duckdb.DuckDBStore`). An engine-free base, with
every engine an extra (#1288), waits on a table store that does not need it.

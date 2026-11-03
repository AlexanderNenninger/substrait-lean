### The SQL written for DuckDB is proved to return the reference's rows or raise

`Rel.duckdb_shim_sound` (`SubstraitLean/Profile.lean`) proves that DuckDB,
running the SQL sverify writes, returns `Rel.eval`'s rows or raises, for any
plan, with no contract needed (#185). Engine profiles state what DuckDB
computes for each function, and where it differs from the reference the
written SQL compensates ([engine profiles](../docs/engine-profiles.md)). The
query catalogue records, for each benchmark query, whether it is verified SQL
on DuckDB (`verified_sql` in [`catalogue/INDEX.md`](../catalogue/INDEX.md),
#229).

### Every engine is a plugin

Sverify finds its engines in the entry-point group `sverify.profiles` and
nowhere else, its own among them: DuckDB, Polars, Spark, DataFusion and
Snowflake's dialect register a `ProfilePlugin` there, as a package from
outside does ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
`ProfilePlugin` gains optional fields for a runner (`runner`, `local`,
`optional`, `session`, `modules`, `read_settings`) and a SQL dialect
(`dialect`), so an engine from outside gets `connect`, `run` and `to_sql` as
the built-in ones have them. Entries for one engine merge field by field
([Engine profiles from outside](docs/engine-profiles.md#engine-profiles-from-outside)).
After upgrading an editable install, run `uv sync` so its metadata carries
the entry points.

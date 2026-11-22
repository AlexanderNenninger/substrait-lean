### `ProfilePlugin.sql`: a dialect's SQL front-end (#1362)

A plugin can read a SQL dialect: `ProfilePlugin(sql=SQLFrontEnd(read, lift))`.
`sverify.sql(dialect=)` looks the dialect up among the installed plugins (an
unknown one names those installed), and DuckDB's own lift is registered the same way.
The dialect's semantics is the engine's name, accepted only where the plugin brings
the checker's profile. A report of SQL read by a front-end other than DuckDB's names
its package and version. `PLUGIN_API` is 4: engine packages need the same release.

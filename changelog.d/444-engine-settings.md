### Engine settings checked before a routed run (#444)

A profile's facts hold under the engine's default settings. Before
`Report.run(..., route=...)` or `refresh(route=...)` runs, sverify reads
the settings the plan will run under and compares them with those the
facts were probed under. A setting a choice depends on refuses the run
with the setting named (`sverify.errors.EngineSettingsError`): on DuckDB
`default_null_order`, `default_order`, `integer_division`,
`error_on_division_by_zero` and `ieee_floating_point_ops`, on Polars the
engine affinity (`pl.Config.set_engine_affinity`, probed in memory). A
DuckDB `TimeZone` other than UTC or Europe/Berlin warns
(`EngineSettingsWarning`). DuckDB's settings are read on the cursor sverify
runs plans on, so a `SET GLOBAL`, or a `SET` of a global-only setting, is
seen; a session's `SET` on another cursor is not.

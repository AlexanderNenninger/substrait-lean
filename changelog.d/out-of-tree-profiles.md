### Engine profiles from outside sverify

A package can add an engine profile without changing sverify: its Lean side
builds a checker over `builtinEngines` and its own `EngineProfile`, checked
by `#check_engine_profiles`, and its Python side registers a
`sverify.profiles.ProfilePlugin` under the entry-point group
`sverify.profiles`. Installed, `verify(semantics=<engine>)` and the routes
take it in, with its settings and version checks ([Engine profiles from
outside](docs/engine-profiles.md#engine-profiles-from-outside)).
`ProfilePluginWarning` reports an entry point that does not load.

### Profiles come from the installed plugins

- `verify(semantics=...)` takes the reference, DuckDB's semantics and every
  installed engine profile, as the plugins declare them:
  `sverify.profiles.ProfilePlugin.profile`, which defaults to whether the
  plugin brings a checker of its own, so a profile package from outside
  sverify keeps working unchanged. Substrait's own profile is a built-in
  plugin (`substrait`). `sverify.contracts.semantics_names()` lists what is
  installed ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
- `sverify.report.Semantics` and `sverify.engine.Engine` are now `str`, no
  longer `Literal` types that listed the built-in names.

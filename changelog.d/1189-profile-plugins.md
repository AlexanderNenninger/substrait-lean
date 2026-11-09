### Profiles come from the installed plugins

- `verify(semantics=...)` takes the reference, DuckDB's semantics and every
  installed engine profile, as the plugins declare them: a
  `sverify.profiles.ProfilePlugin` sets `profile=True` where the checker has
  its engine's profile. Substrait's own profile is a built-in plugin
  (`substrait`). `sverify.contracts.semantics_names()` lists what is
  installed ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
- Breaking: a profile plugin from outside sverify must set `profile=True` to be
  verified under; carrying `versions` no longer marks it. `sverify.report.Semantics`
  and `sverify.engine.Engine` are now `str`, no longer `Literal` types that
  listed the built-in names.

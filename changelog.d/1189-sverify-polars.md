### Polars is a package of its own: sverify-polars

sverify's Polars engine moves into the distribution `sverify-polars`
(`engines/polars/`, package `sverify_polars`), released with sverify at its
version ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
`pip install sverify[polars]` installs it, and with it Polars and NumPy, as
before. It registers its `ProfilePlugin` in the entry-point group
`sverify.profiles` as a package from outside does. Polars's facts and probes
move with it, to `engines/polars/facts/` and `engines/polars/probes/`.

`sverify.polars_engine` is now `sverify_polars.engine`, and
`sverify._polars_shims` is `sverify_polars.shims`.

`ProfilePlugin` gains three optional fields, so an engine package provides
what sverify asked of Polars by name before: `run_tables` (a run over Arrow
tables, which `sverify.engines.run_sharded` uses), `guard_free_theorem` (the
theorem behind a run without the checks a contract report discharged) and
`fallbacks` (the nodes a plan runs outside the engine's chosen executor,
which `streaming="require"` refuses).

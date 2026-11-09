# sverify-polars

Polars as an engine of [sverify](https://github.com/AlexanderNenninger/substrait-lean):
a plan verified in Lean runs as a Polars lazy frame on Polars's streaming
engine, with a shim where Polars differs from the reference. Install it with
`pip install sverify[polars]`, which brings Polars and NumPy (`sverify-polars[run]`);
`sverify-polars` alone carries the plugin and the facts, for verifying under
`semantics="polars"` without Polars. sverify finds it through its
`ProfilePlugin` in the entry-point group `sverify.profiles`.

The directory is one engine package of #1189:

- `src/sverify_polars/`: the plugin (`PLUGIN`), the translation to lazy
  frames (`engine`) and the shims (`shims`);
- `facts/`: what Polars does at each of the core's options, the evidence
  for `Profile.polars` ([facts/README.md](facts/README.md));
- `probes/`: the probes' recordings the facts cite;
- `tests/`: its tests, which run in sverify's test session
  (`python/pyproject.toml`'s `testpaths`).

Its Lean half (the profile and the lowering, `Sverify.Polars`) follows.

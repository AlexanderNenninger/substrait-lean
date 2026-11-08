### Verified plans run on Polars without the checks the proof discharged

- `Report.run` on Polars leaves out the per-row run-time checks of a
  guard-free plan once it has checked the preconditions on the batch
  (`guard_free`, `Rel.polars_sound`). The checks of assumed `SUM`s and of
  `±∞` stay. On the catalogue's 52 proved plans, Polars's plans hold 107 guard
  columns where they held 206
  ([#1166](https://github.com/AlexanderNenninger/substrait-lean/issues/1166)).
  With `check_requires=False`, and on the other engines, every check stays.
- `sverify.engines.run` takes `guards=`, as `to_sql` does.

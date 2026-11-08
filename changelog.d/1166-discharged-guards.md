### Verified plans run without the checks the proof discharged

- `Report.run` on DuckDB and Polars leaves out the per-row run-time checks the
  checker proved unnecessary on data that meets the preconditions, once it
  has checked them on the batch (`guard_free`, `unchecked`,
  `Rel.guardFree_sound`). The checks of assumed `SUM`s and of `±∞` stay. On
  the catalogue's 52 proved plans, DuckDB's SQL holds 42 checks where it held
  170, and Polars's plans 107 guard columns where they held 206
  ([#1166](https://github.com/AlexanderNenninger/substrait-lean/issues/1166)).
  With `check_requires=False` every check stays.
- `sverify.engines.run` takes `guards=` and `unchecked=`, as `to_sql` does.

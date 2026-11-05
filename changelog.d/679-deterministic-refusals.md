### Deterministic runs name the open ties

`choose(deterministic=True)`, an incremental refresh and a sink's
`reproducible=` ask for the deterministic profile (D24,
[#679](https://github.com/AlexanderNenninger/substrait-lean/issues/679)). A
plan whose ties stay open is refused there, and the reason names each window,
ordered aggregate or `LIMIT` (`Report.tie_places`). Without them the plan
runs with the engine's own order of the ties, which every proof covers. The
catalogue accepts any order the reference allows (`substrait-check
--eval-choices`, `sverify.testing.lean_choices` and `allows_rows`), so
`iot-downsample` and `pa-string-agg` match on DuckDB without `tie_order`.

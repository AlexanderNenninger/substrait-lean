### SQL lift: named `WINDOW`, `any_value` and `DATE ± INTEGER`

The DuckDB SQL lift reads `WINDOW w AS (…)` with `OVER w` and `OVER (w ORDER BY …)`, `any_value(x)` (a non-NULL value of the group, reported as the engine's choice) and `DATE ± <integer constant>` (a DATE). `arg_min_null`, `bitstring_agg` and `histogram_exact` are refused with the reason and [#326](https://github.com/AlexanderNenninger/substrait-lean/issues/326); `DATE ± <integer column>` and `DISTINCT ON` stay refused with their rewrite ([#319](https://github.com/AlexanderNenninger/substrait-lean/issues/319)).

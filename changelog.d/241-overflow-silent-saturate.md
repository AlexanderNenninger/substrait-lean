### Integer overflow can wrap around or clamp when a plan asks

A plan may now set `overflow` to `SILENT` (wrap around) or `SATURATE` (clamp)
on integer `add`, `subtract`, `multiply` and `negate`, at the declared width
(`i8` to `i64`); before, these were refused (#255). Nothing raises for them,
so `verify` reports no overflow. DuckDB runs them in 128-bit arithmetic, with
templates the Lean lowering generator found and proved (`SATURATE`) or a
hand-written, proved schema (`SILENT`); the other engines refuse them for now
([#241](https://github.com/AlexanderNenninger/substrait-lean/issues/241)).

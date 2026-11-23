### `VAR_*`, `STDDEV_*` and `COVAR_*` read `float_overflow`

The function groups `agg.var` and `agg.stat` now list `float_overflow`, as
`agg.fsum` does, so each engine's table states what it gives where a
variance or covariance of finite doubles overflows: `+inf` on DuckDB, Polars
and Spark (their facts' new probes,
[#1601](https://github.com/AlexanderNenninger/substrait-lean/issues/1601)). The
reference already raises there (`AggFn.infAgg`); a `#guard` in
`Infer.lean` now ties the two lists. Results are unchanged.

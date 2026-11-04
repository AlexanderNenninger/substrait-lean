### Exact median, quantiles, mode and arg_min/arg_max

Sverify now verifies the exact quantiles, the mode and `arg_min`/`arg_max`
([#53](https://github.com/AlexanderNenninger/substrait-lean/issues/53)), from
Ibis (`median()`, `quantile(q)`, `mode()`, `argmin()`, `argmax()`) and from
DuckDB's SQL (`median`, `quantile_cont`, `quantile_disc`, `quantile`,
`mode(x ORDER BY …)`, `arg_min`, `arg_max`), and runs them on DuckDB:

- `quantile_disc(x, q)` is the value at position `⌈n·q⌉` of the values in
  order; `quantile_cont(x, q)` and `median(x)` interpolate between the two
  neighbours at `(n−1)·q`, of doubles or of integers converted. `q` is an
  exact decimal in `[0, 1]`. Contracts know a median or quantile lies within
  its column's range.
- `mode` breaks ties by its own `ORDER BY`, and is refused without one;
  Ibis's `mode()` takes the smallest of the most frequent values.
- `arg_min(x, y)` is `x` at the row with the smallest `y`, over the rows where
  neither is NULL; ties are the engine's choice unless a key settles them, as
  for `first()`.

What DuckDB 2.0.0 does with each is recorded as engine facts
(`duckdb-quantile-disc`, `duckdb-quantile-cont-interpolation`,
`duckdb-mode-ties`, `duckdb-arg-min-nulls`). Other engines refuse them until
[#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271), and
approximate quantiles stay refused
([#469](https://github.com/AlexanderNenninger/substrait-lean/issues/469)).
H2O's groupby q6 and the catalogue's median and arg_max queries now verify.

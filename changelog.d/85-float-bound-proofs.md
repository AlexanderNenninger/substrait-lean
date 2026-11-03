### Proved error bounds for floating-point aggregates

The `float-bounds/` package proves error bounds for `SUM`, `AVG`, `VAR_*`,
`STDDEV_*`, `COVAR_*` and `CORR` of doubles (#85), in the standard model of
rounding with its underflow term. A sum of `n` values is within
`γ n · Σ(|xᵢ| + 2⁻¹⁰²²)` of the exact one, sequentially or in shards; the
co-moment behind the variance family is within `64 · n² · u · B²` for each of
the two-pass, textbook and Welford/Chan algorithms (DuckDB's), so the bound
holds whatever an engine uses. See `docs/float-bounds.md`.

### Generic properties of statistical aggregates

`VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` now have proved generic properties
that any common algorithm keeps (#85): `NULL` where the reference says, a
variance `≥ 0`, the result within `(128 n² u B² + 12 n u B²) / d` of the
exact one, and `|CORR| ≤ 1 + ε` when both variances are bounded below. The
reference allows any result with them (`StatProps`), so DuckDB's Welford,
Polars' blockwise two-pass and the reference's own two-pass all agree with
it. Engine profiles can name a stricter algorithm (`Profile.statAlgo`).
A computed double's bound now carries through `CAST(x AS BIGINT)` with row
caps, and `SUM(CAST(x AS DOUBLE))` of integers gets the summation bound.
See "Statistical aggregates" in `docs/reference-semantics.md`.

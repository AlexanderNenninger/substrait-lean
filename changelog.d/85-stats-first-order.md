### Statistical aggregates within bounds that scale with the spread

`VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` may now differ from the exact result
only by bounds that scale with the spread of the values (`StatProps`,
`docs/reference-semantics.md`). For `10⁶` values near `10⁶` that vary by about
`1`, the variance is within about `2 · 10⁻²`, where the earlier bound allowed
`1.4 · 10⁴`. The bounds are proved for two-pass and for DuckDB's algorithm;
the textbook formula `Σx² − (Σx)²/n` falls outside them.

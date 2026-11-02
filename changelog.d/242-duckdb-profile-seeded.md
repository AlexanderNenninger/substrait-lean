### DuckDB's profile says what DuckDB computes, and the lowering compensates

`Profile.duckdb` now states DuckDB 2.0's behaviour where the probes found it
differs from the reference: NaN for operations on doubles that have no value
(`∞ - ∞`, `0 · ∞`, `∞ / ∞`, `sqrt(-1)`), `-∞` for a logarithm of 0, IEEE
division by zero for doubles (`ieee_floating_point_ops`, a new setting),
`atan2(0, 0) = 0`, `MIN % -1` raising, and the shifts. The generated lowering
to DuckDB guards each of them, every guard proved by the kernel, and
`Rel.duckdb_sound` is restated for DuckDB's IEEE mode, with the SQL printer
trusted for `MIN % -1` and `<<`, which it writes out. The lowering generator
keeps its results in `SubstraitLean/LoweringCache.lean`
(`substrait-check --lowering-cache`), so builds try each known template first
(#242).

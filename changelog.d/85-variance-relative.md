### Variance bounds that scale with the spread

`float-bounds/` proves tighter variance bounds for three algorithms (#85):
two-pass, Lean's own, is within `8 n u S + 80 n² u² Σx²` of the exact sum of
squared deviations `S`, Welford's update within one thread within
`32 n u √(S Σx²) + 104 n² u² Σx²`, and DuckDB's parallel aggregation (Welford
in each thread, Chan's merge with a fused multiply-add) within
`148 n u √(S Σx²) + 3961 n² u² Σx²`. The covariance has the analogues, for
two-pass and for DuckDB's parallel aggregation, in `√(S_xx S_yy)`,
`√(Σx² S_yy)` and `√(Σy² S_xx)`. They stay useful for values far from zero
with a small spread, where the generic bound does not. The
standard model of rounding now states that a double rounds to itself.

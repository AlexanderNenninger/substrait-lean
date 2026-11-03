### Variance bounds that scale with the spread

`float-bounds/` proves tighter variance bounds for two algorithms (#85):
two-pass, Lean's own, is within `8 n u S + 80 n² u² Σx²` of the exact sum of
squared deviations `S`, and Welford's update within one thread, DuckDB's,
within `32 n u √(S Σx²) + 104 n² u² Σx²`. Both stay useful for values far
from zero with a small spread, where the generic bound does not. The
standard model of rounding now states that a double rounds to itself.

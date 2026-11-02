### `round(x, d)` at every number of digits

`round(x, d)` of a double now means what DuckDB computes for every `d`
(#335): below zero it divides by an exact power of ten and multiplies back,
so `round(42.0, -1000)` is 0, not NaN, and `round(521924.889, -5)` is
`500000.0`, not `499999.99999999994`. A result that would not be finite
falls back to 0 (for `d < 0`) or to `x` (for `d ≥ 0`). The plans sverify
writes now include `round` with digits for a double literal, which they
refused before ("unsupported function round/2"). DataFusion rounds
otherwise, so it refuses `round(x, d)` until #271.

### Fixes

- On Polars, a window `SUM` or `AVG` whose frame holds both `+inf` and `-inf`
  is NaN again, as in the reference and on DuckDB; a merge had made it raise a
  domain error.

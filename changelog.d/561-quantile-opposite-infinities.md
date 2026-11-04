### `QUANTILE_CONT` between `-inf` and `+inf` raises (#561)

`QUANTILE_CONT` and `MEDIAN` whose neighbouring values are `-inf` and `+inf`
now raise a domain error in the reference, as a NaN created from numbers does
(`AggFn.makesNan`). IEEE's interpolation, and DuckDB's, is NaN there; the
reference used to clamp it to `+inf`, so engines disagreed. A plan that may
meet it is reported as a possible domain error, ruled out by a precondition
that bounds the column, and the SQL sverify writes for DuckDB raises where
the interpolation is NaN and no value is. Per D17, this changes the reference
and ships in a minor version bump.

### `QUANTILE_DISC` of doubles may return any zero or NaN of its class (D45)

The reference now treats `QUANTILE_DISC` as it treats `MIN` and `MAX` (D31).
Where the selected value is a zero or a NaN, any member of its class in the
group, or the class's canonical value, is allowed (`AggFn.Picks`). DuckDB
returns `-0.0` or `+0.0` by row order and thread count, and both are now
results the reference allows. No verdict changes.

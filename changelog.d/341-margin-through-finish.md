### The margin check reads DuckDB's finish of `SUM` and `AVG`

Under `semantics="duckdb"`, a threshold on a double `SUM` or `AVG` that DuckDB
finishes with a `CASE` (NaN, `+∞` or the sum) has the margin check again. The
`CASE`'s conditions must compare a key, a count, an integer sum, a minimum or a
maximum with a constant, combined with `and` and `not`; a condition that reads a
variance, a quantile or another measure the engines compute differently has no
check (#341, #929).

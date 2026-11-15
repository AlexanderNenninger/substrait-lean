### DuckDB's SUM and AVG of doubles with both infinities are no domain error

Under `semantics="duckdb"`, a `SUM` or `AVG` of doubles holding `+∞` and `-∞`
is NaN, as DuckDB computes it, and `verify` no longer reports a domain error
for it ([#341](https://github.com/AlexanderNenninger/substrait-lean/issues/341)).
The generated lift writes the aggregate as a sum that never sees `+∞` or NaN
and the largest and smallest value, finished by a `CASE` that gives NaN or
`+∞` where they say so; Lean proves it equals `SUM` or `AVG` of the values,
and that none of its measures has a domain error. Under the reference semantics the
aggregate and its domain error are unchanged. The written SQL has three
aggregates where DuckDB's has one, until the generated lowering folds the
pattern back (#271).

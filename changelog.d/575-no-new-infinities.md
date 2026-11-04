### Doubles: no operation creates `±∞` (#575)

The reference now raises where an operation on finite doubles overflows to
`±∞`: `+`, `-`, `*`, `/` and `power` (`1e308 * 10`, `power(0, -1)`), `exp`
past `709.78`, and a `SUM`, `AVG`, variance or covariance of finite values.
`verify` rules the error out by an inferred precondition, as for a `SUM` that
leaves 64 bits: a `SUM` or `AVG` of bounded values over a bounded number of
rows (`max_rows`) is proved finite (#85's error bounds), and elsewhere
`Report.assumed` lists the precondition ("stays finite where its inputs
are") and the job checks it on the data: the SQL sverify writes for DuckDB
raises `overflow to infinity` where it fails, and so does the Polars engine.
With `infer=False` it is an error that makes the report unproved. A plan verified
with `semantics="duckdb"`, where DuckDB's `±inf` is the answer, makes no such
assumption, and `Report.run` writes no check of it. `±∞` from
the data passes through as before. So a plan verified under the reference
creates no NaN and no `±∞` its inputs did not hold
([#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575),
fact `duckdb-double-overflow`, spec gap `ST-9`).

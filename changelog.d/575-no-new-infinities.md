### Doubles: no operation creates `±∞` (#575)

An operation on finite doubles whose result overflows to `±∞` is now an
assumption a report makes and the job checks: `+`, `-`, `*`, `/` and `power`
(`1e308 * 10`, `power(0, -1)`), `exp` past `709.78`, and a `SUM`, `AVG`,
variance or covariance of finite values. `Report.assumed` lists each one
("stays finite where its inputs are"), the SQL sverify writes for DuckDB
raises `overflow to infinity` where one fails, and so does the Polars engine.
With `infer=False` they are errors. A `SUM` or `AVG` of bounded values over a
bounded number of rows (`max_rows`) is proved finite (#85's error bounds) and
needs no assumption. `±∞` from the data passes through as before. So a plan
verified under the reference creates no NaN and no `±∞` its inputs did not
hold ([#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575),
fact `duckdb-double-overflow`, spec gap `ST-9`).

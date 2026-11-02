### `AVG` of a DECIMAL over a window as a double

`avg(d) OVER (...)` of a DECIMAL column in DuckDB SQL is now verified, as a
DOUBLE the way DuckDB types it, and arithmetic with it is in doubles (as in
TPC-DS q89's `sum_sales - avg_monthly_sales`).

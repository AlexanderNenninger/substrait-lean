### A grouped double `SUM` or `AVG` runs faster on DuckDB

Sverify checks a double `SUM` or `AVG` for both infinities among its values and for finite values that overflow. On DuckDB it now runs those checks only for the groups whose sum is not finite, in a second stage joined back on the keys (#1608, #1787). On 10 million rows the written query takes 0.11 s where it took 0.37 s, and 0.23 s where it took 0.46 s behind a join; with every group infinite it takes the same time as before.

A finite sum has finite values. Lean proves this for sums added in any tree or in sequence (`SumOrder.isFinCode`). For DuckDB's constant runs and Polars's compensated sum it is a probed engine fact (`duckdb-sum-double`, `polars-sum-float`). The two-stage SQL is tested against the one-stage SQL (`tests/test_two_stage_sums.py`). The group keys stay as written; doubles as keys, window sums and the other engines keep one stage.

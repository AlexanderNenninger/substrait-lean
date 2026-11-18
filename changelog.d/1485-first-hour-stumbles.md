### First-hour stumbles

`sverify check revenue.sql` exits 2 and says to check SQL through `sv.sql` in a `.py` file or a dbt project, in place of "not a Python file" and exit 6. The internal `DOUBLE(…)` cast no longer shows around an aggregate, and the check's output no longer ends with a bare status line after the node's own verdict. A counterexample prints a date or timestamp in the output as a date or timestamp, as the input does, which also fixes sverify-dbt's `order_date = 0`. The `SUM` hint leads with the run-time check, and its example row cap is one anyone would write (#1485).

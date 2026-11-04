### Rankings with their own ORDER BY are refused

The SQL lift refuses `rank`, `dense_rank`, `row_number`, `percent_rank` and `cume_dist` with an `ORDER BY` of their own (`cume_dist(ORDER BY id) OVER (… frame)`), which DuckDB ranks within the frame. They were lifted as a plain rank over the partition, a wrong result in Lean and in the written SQL ([#625](https://github.com/AlexanderNenninger/substrait-lean/issues/625)).

### Window functions on Polars run natively

- Ranks, `NTILE`, `PERCENT_RANK`, `CUME_DIST`, frame aggregates and
  `FIRST_VALUE`, `LAST_VALUE`, `NTH_VALUE` run as Polars expressions on the
  streaming engine, with no Python in the window path. A running `SUM` over
  10⁵ rows takes 16 ms instead of 93 s
  ([#PRNUM](https://github.com/AlexanderNenninger/substrait-lean/pull/PRNUM)).
- A double `SUM` or `AVG` over a frame adds the frame's own values: a running
  sum for frames from the partition's first row, blocks of rows otherwise.
  The Polars profile's `window_sum_algo` is `RUNNING_ADD` and `TREE`, within
  the plan's bound as before (polars-window-agg). Polars's own
  `rolling_sum`, a sliding sum whose result is no sum of the frame, is not
  used.
- A `RANGE` frame with offsets over a date or timestamp key runs per
  partition; without `PARTITION BY`, its bounds take one in-memory step
  (`search_sorted`).

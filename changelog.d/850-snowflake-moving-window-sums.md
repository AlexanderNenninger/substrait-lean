### Fixes

- Sverify's Snowflake SQL for a window `SUM` or `AVG` of doubles over a
  moving frame could give a value outside the plan's bound (Snowflake
  behaviour recorded privately). Such a frame's values are now collected
  (`ARRAY_AGG`) and added anew (`REDUCE`), within the plan's bound. Running
  and whole-partition sums keep Snowflake's `SUM`.

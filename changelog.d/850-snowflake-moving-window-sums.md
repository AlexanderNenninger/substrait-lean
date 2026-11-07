### Fixes

- Sverify's Snowflake SQL for a window `SUM` or `AVG` of doubles over a
  moving frame (`ROWS BETWEEN 2 PRECEDING AND CURRENT ROW`, a `RANGE` offset)
  could give a value no order of the frame's own values gives: Snowflake
  subtracts the rows that leave the frame, so a large value long gone keeps
  its rounding in the result, and a frame of `0.0` and `0.0` came back
  `-0.5` (Snowflake behaviour recorded privately). Such a frame's values are
  now collected (`ARRAY_AGG`) and added anew (`REDUCE`), within the plan's
  bound. A running sum (`UNBOUNDED PRECEDING` to `CURRENT ROW`) and the whole
  partition keep Snowflake's `SUM`.

### Snowflake SQL: time frames and set operations compile

Sverify's Snowflake SQL ran every written plan on Snowflake 10.40.103 again
(#849), and two kinds of plan failed to compile:

- A `RANGE` frame with offsets over a timestamp (a rolling window of five
  minutes) wrote its offset as a number of microseconds, which Snowflake
  refuses (`010057`); an `INTERVAL` takes whole milliseconds at most and cuts
  finer offsets. The frame now orders by the key in microseconds since the
  epoch and takes the offset exactly.
- `INTERSECT` and `EXCEPT`, whose rows compare with NULL equal to NULL, failed
  on some tables with `002031 Unsupported subquery type`. The comparison is
  now Snowflake's `EQUAL_NULL`.

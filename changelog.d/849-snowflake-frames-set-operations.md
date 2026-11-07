### Snowflake SQL: time frames and set operations compile

Two kinds of plan in sverify's Snowflake SQL did not run on Snowflake
(Snowflake behaviour recorded privately, #849):

- A `RANGE` frame with offsets over a timestamp (a rolling window of five
  minutes) wrote its offset as a number of microseconds. The frame now orders
  by the key in microseconds since the epoch and takes the offset exactly.
- `INTERSECT` and `EXCEPT`, whose rows compare with NULL equal to NULL, now
  write the comparison as Snowflake's `EQUAL_NULL`.

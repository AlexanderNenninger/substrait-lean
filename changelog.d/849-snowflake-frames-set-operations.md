### Snowflake SQL: time frames and set operations

Sverify's Snowflake SQL changes for two kinds of plan (Snowflake behaviour
recorded privately, #849):

- A `RANGE` frame with offsets over a timestamp (a rolling window of five
  minutes) orders by the key in microseconds since the epoch and takes the
  offset as that number, exactly.
- `INTERSECT` and `EXCEPT`, whose rows compare with NULL equal to NULL, write
  the comparison as Snowflake's `EQUAL_NULL`.

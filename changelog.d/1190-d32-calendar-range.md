### Calendar functions from 0001 to 9999 (D32)

- `date_part`, `date_trunc` to a week, month, quarter or year, `date_bin`,
  `strftime` and adding months work on every timestamp from 0001-01-01 to
  9999-12-31 on DuckDB, Polars and Spark. Truncations used to raise outside
  1677 to 2262, DataFusion's nanosecond range.
- A DATE or TIMESTAMP value lies in 0001 to 9999 by its type. Reading a
  table whose DATE or TIMESTAMP column holds a value outside it fails,
  naming the column, how many values and one of them. A computed date or
  timestamp outside it raises "outside the reference's timestamps" in a
  calendar function; a column read needs no guard or precondition.
- A `date_bin` origin outside 0001 to 9999 is refused when the plan is
  checked.
- DataFusion refuses calendar truncation and `date_bin`
  (`upstream/bugs/DF-17.json`).

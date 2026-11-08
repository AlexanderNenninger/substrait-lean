### Calendar functions from 0001 to 9999 (D32)

- `date_part`, `date_trunc` to a week, month, quarter or year, `date_bin`,
  `strftime` and adding months work on every timestamp from 0001-01-01 to
  9999-12-31 on DuckDB, Polars and Spark. Truncations used to raise outside
  1677 to 2262, DataFusion's nanosecond range.
- Outside 0001 to 9999 they raise "outside the reference's timestamps",
  `date_part` included, which used to give NULL past chrono's years. A
  `date_part` of a timestamp without a range contract gets a per-row guard;
  a range in `requires` removes it.
- A `date_bin` origin outside 0001 to 9999 is refused when the plan is
  checked.
- DataFusion refuses calendar truncation and `date_bin`
  (`upstream/bugs/DF-17.json`).

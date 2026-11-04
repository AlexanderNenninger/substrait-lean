### Engine sums, transfers up to an order, and a LIMIT over ties

- DuckDB's and Polars's double `SUM` and `AVG` are within #85's bound of the
  reference's, not one of its orders: DuckDB merges partial sums in finishing
  order and adds a constant vector as one product; Polars's in-memory groups
  use Kahan's sum
  ([#633](https://github.com/AlexanderNenninger/substrait-lean/issues/633)).
- The transfer check between profiles (`--transfer`, a route's transfer)
  accepts a behaviour below the one the proof used, such as a sequential sum
  where the proof allowed any order.
- A contract's dependency report leaves out the value choices of columns
  nothing reads.
- A `LIMIT` below an `ORDER BY` that ties, or with none, makes the report
  not deterministic
  ([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444), D10).

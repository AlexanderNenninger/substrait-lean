### `-0.0` as the engines compute it

- The reference computes doubles as IEEE 754 does, `-0.0` included:
  `0.0 * -1.0` is `-0.0`, and an `AVG` that underflows may be `-0.0`.
  Comparisons, `ORDER BY`, `DISTINCT`, `GROUP BY`, join keys and window
  partitions read `-0.0` as `0.0` and every NaN as the NaN, as DuckDB, Spark
  and Polars do ([core semantics](../docs/core-semantics.md)).
- A `DISTINCT` row, a `GROUP BY` key and a `MIN` or `MAX` may be any member
  of its class in the input, or the class's canonical value: a group of
  `-0.0`s may come out as `0.0`, as Spark and DuckDB give it. Plans whose
  keys and arguments hold no doubles keep one result.
- `x / -0.0` and `x % -0.0` raise as `x / 0.0` does. DuckDB's profile gives
  IEEE's signed `±∞` for them, and its `atan2` of signed zeros C's value.
- Substrait's `divide` with `on_division_by_zero: IEEE` on doubles is IEEE
  division: `1.0 / -0.0` is `-∞`. `0.0 / 0.0` and `∞ / ∞` raise in the
  reference, as every operation that would create a NaN does; DuckDB and
  Polars give NaN. The DuckDB SQL lift writes `/` of doubles this way under
  `semantics="duckdb"`, and Polars runs it natively.
- Which zero `round` and `ceil` give a negative value that rounds to zero is
  left open (`round_zero_sign`): DuckDB and Polars give `-0.0`, Spark `+0.0`,
  and the reference `0.0`. Results are compared up to the sign of a zero
  there.
- Incremental `GROUP BY`, `DISTINCT`, `MIN` and `MAX` keep one state row per
  class of keys, with its canonical key; Lean proves the maintained view is
  one the reference allows.
- `decode_double` gives `-0.0` for its code. Parquet statistics bound
  canonical values, so a file whose minimum is `0.0` still prunes correctly
  when it holds `-0.0`.

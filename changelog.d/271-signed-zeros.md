### `-0.0` as the engines compute it

- The reference computes doubles as IEEE 754 does, `-0.0` included:
  `0.0 * -1.0` is `-0.0`, and an `AVG` that underflows may be `-0.0`.
  Comparisons, `ORDER BY`, `DISTINCT`, `GROUP BY`, join keys and window
  partitions read `-0.0` as `0.0` and every NaN as the NaN, as DuckDB, Spark
  and Polars do (D31 in `docs/core-semantics.md`).
- A `DISTINCT` row, a `GROUP BY` key and a `MIN` or `MAX` may be any member
  of its class in the input, or the class's canonical value: a group of
  `-0.0`s may come out as `0.0`, as Spark and DuckDB give it. Plans whose
  keys and arguments hold no doubles keep one result.
- `x / -0.0` and `x % -0.0` raise as `x / 0.0` does. DuckDB's profile gives
  IEEE's signed `±∞` for them, and its `atan2` of signed zeros C's value.
- Substrait's `divide` with `on_division_by_zero: IEEE` on doubles reads as
  IEEE division (D39): `1.0 / -0.0` is `-∞`. Under DuckDB's profile
  `0.0 / 0.0` is NaN; the reference keeps raising on it (D37). The DuckDB
  SQL lift gives `DOUBLE / DOUBLE` this function. Polars refuses the
  option, so Ibis's `cot` is refused on Polars.
- Incremental `GROUP BY`, `DISTINCT`, `MIN` and `MAX` keep one state row per
  class of keys, with its canonical key; Lean proves the maintained view is
  one the reference allows.
- `decode_double` gives `-0.0` for its code. Parquet statistics bound
  canonical values, so a file whose minimum is `0.0` still prunes correctly
  when it holds `-0.0`.

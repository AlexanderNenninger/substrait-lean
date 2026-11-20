### float32 columns, interval casts, and unread columns under SQL conditions

- Sverify reads float32 (`REAL`) columns and constants: it passes them through,
  compares, orders and groups them, takes their `min` and `max`, and casts them
  to double. A run returns float32 where `Report.output` says float32, on every
  engine, and a float32 constant arrives bit for bit. Every use whose result
  depends on the width stays refused with the step named: arithmetic, `SUM`, `AVG`
  and the statistical aggregates, `round`, and casts to strings, decimals and
  `REAL` ([#1908](https://github.com/AlexanderNenninger/substrait-lean/issues/1908),
  [#417](https://github.com/AlexanderNenninger/substrait-lean/issues/417), ruling 186).
- In SQL, a `REAL` next to an integer or decimal constant is compared as a `REAL`, as
  DuckDB does (`0.3::REAL = 0.3` is true; fact `duckdb-coerce-real`). The constant is
  rounded once, as DuckDB rounds it; one that would round twice (an integer past 2^53,
  a decimal whose nearest double is halfway between two singles) is refused.
- A double constant `-0.0` keeps its sign in the written plan and on Polars.
- An integer cast to an interval of weeks, days, hours, minutes or seconds,
  `n.cast("interval('D')")`, is read as `n.as_interval("D")`
  ([#1926](https://github.com/AlexanderNenninger/substrait-lean/issues/1926)).
- A SQL `ensures` condition on an Ibis transformation no longer fails on a binary
  or map column that nothing reads
  ([#1958](https://github.com/AlexanderNenninger/substrait-lean/issues/1958)).
- Binary values are refused by design, with advice that holds on every engine:
  encode them as text at the source (hex or base64), or leave the column out
  ([#1918](https://github.com/AlexanderNenninger/substrait-lean/issues/1918)).

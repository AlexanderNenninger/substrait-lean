### Snowflake SQL, checked against a live Snowflake

Sverify's Snowflake SQL was run on Snowflake 10.40.102 (#63), and the writer
changes where it did not give the reference:

- A string's raise (`UPPER` or `LOWER` of non-ASCII text, `repeat` past
  2^31 bytes) returned its message as the value, since a cast to `VARCHAR`
  never fails. It now raises.
- `SUBSTR` reads positions and lengths as 32-bit integers: a start of
  2^32 - 1 picked the last character. Starts and lengths are clamped below
  2^31, and a start from 2^32 on raises as on the other engines.
- `VAR_*` and `STDDEV_*` of doubles are refused: Snowflake's give 0 for
  `1e9 + {4, 7, 13, 16}`, whose variance is 30.
- A modulus of doubles is refused: Snowflake's `MOD` computes
  `a - b * TRUNC(a / b)` in doubles, so `MOD(1e308, 9.13e10)` is 0 where the
  remainder is 3.8e10.
- Semi, anti and outer joins failed to compile (`002031 Unsupported subquery
  type`): a correlated `EXISTS` now has its condition bare in the `WHERE`.
- `strpos` is Snowflake's own `POSITION`, which gives 1 for an empty needle
  and NULL for NULLs, and integer arithmetic of literals folds when the SQL is
  written. The strings fixture's Snowflake SQL drops from 57 kB to 26 kB.

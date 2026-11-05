### Snowflake, checked against a real Snowflake

Sverify's Snowflake SQL now rests on probes of Snowflake 10.40.102
(`characterization/snowflake/`): 312 queries and 74 facts, which settle every
row of the engine choice tables. Four findings are upstream bugs, SF-1 to
SF-4. The writer changes with them:

- A string's raise (`UPPER` or `LOWER` of non-ASCII text, `repeat` past
  2^31 bytes) returned its message as the value, since a cast to `VARCHAR`
  never fails. It now raises.
- `SUBSTR` wraps positions and lengths at 32 bits (SF-2): a start of
  2^32 - 1 picked the last character. Starts and lengths are clamped below
  2^31, and a start from 2^32 on raises as on the other engines.
- `VAR_*` and `STDDEV_*` of doubles are refused: Snowflake's give 0 for
  `1e9 + {4, 7, 13, 16}`, whose variance is 30 (SF-4).
- Integer arithmetic of literals folds when the SQL is written, and `strpos`
  is Snowflake's own `POSITION`, which the probes show gives the reference
  for an empty needle and for NULLs. The strings fixture's Snowflake SQL
  drops from 57 kB to 26 kB, the largest coverage case (`find from`) from
  66 kB to 48 kB.

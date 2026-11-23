### `strpos` and `contains` on long strings run in linear time

The checker searched a string for a needle by testing every position, up to `n · m` comparisons. A long, almost-matching needle took DuckDB's `test_contains_long_almost_matching_needle` past the replay's 120 s watchdog. The search now rolls a hash over the string and compares characters only where the hash matches, proved equal to the reference's search (`Text.Find.findFrom_eq_fast`). That replay file takes 6 s, and `strpos`, `contains`, `instr` and `position` on long strings stop being quadratic in `verify` (#2497).

### Snowflake: a regex search of the empty string

Snowflake's SQL writes a regex search as `REGEXP_COUNT(s, p) > 0` instead of `REGEXP_INSTR(s, p) > 0`, which is false on an empty string even when the pattern matches it (`^$`, `x*`), so `re_search` of `''` now gives the reference's TRUE.

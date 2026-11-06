### Regular expressions in SQL: the operator `~` is refused

`s ~ p` and `s !~ p` are refused with a hint to write `regexp_matches(s, p)`:
DuckDB's `~` matches anywhere in the string, and SQLGlot reads it as
`regexp_full_match`
([SG-10](upstream/bugs/SG-10.json)). Patterns outside the supported subset
and `regexp_extract` groups past 9, where DuckDB raises, are refused when
the SQL is lifted
([#808](https://github.com/AlexanderNenninger/substrait-lean/issues/808)).

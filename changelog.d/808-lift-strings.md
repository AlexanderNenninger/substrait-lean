### The SQL lift reads regular expressions, padding and splitting

`sv.sql` queries and dbt models may use `regexp_matches`,
`regexp_full_match`, `regexp_extract`, `regexp_replace`, `right`, `lpad`,
`rpad`, `split_part`, `string_split(s, sep)[n]` and `concat_ws`, as the Ibis
API already could
([#808](https://github.com/AlexanderNenninger/substrait-lean/issues/808)).
`string_split` is a new black box, which Lean evaluates; like the other black
boxes, it runs on DuckDB and other engines refuse it until #271.

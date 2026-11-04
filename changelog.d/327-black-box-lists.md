### Vector and list functions

The SQL lift reads DuckDB's vector functions of lists of doubles as black
boxes ([#327](https://github.com/AlexanderNenninger/substrait-lean/issues/327)):
`list_cosine_similarity`, at least -1, so `verify` proves
`array_cosine_similarity(a, b) >= -1`; `list_cosine_distance` and
`list_distance`, at least 0; `list_inner_product`,
`list_negative_inner_product` and `array_cross_product`. Each may raise, on a
NULL element or lists of different lengths. The `array_*` names are read as
the functions of lists. `list_sum` of integers is exact, a BIGINT as `SUM`'s.
`list_extract`, `list_element` and `array_extract` are read as `l[i]`, and
`array_value(…)` as a list literal. The engine facts `duckdb-list-vectors` and
`duckdb-list-sum` record what DuckDB 2.0.0 does.

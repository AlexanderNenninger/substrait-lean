### GROUP BY ALL over a FROM-first query names itself

`FROM t GROUP BY ALL` (DuckDB's FROM-first form, which selects `*`) is refused with "GROUP BY ALL over `*` ... name the columns in a SELECT" instead of "`*` is not supported yet" (#176).

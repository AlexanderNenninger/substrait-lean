### The report lists an ordering comparison of lists

A DuckDB SQL query that orders lists (`<`, `<=`, `>`, `>=`, `BETWEEN`, `greatest`, `least`) now shows a dialect difference, `list_null_order`, in `Report.dialect_differences`, under every semantics. Where a NULL element decides the order, the plan gives NULL and DuckDB orders the NULL last: `[1,2] < [1,NULL,3]` is NULL here and TRUE on DuckDB (part of [#2163](https://github.com/AlexanderNenninger/substrait-lean/issues/2163)). The verdict is unchanged.

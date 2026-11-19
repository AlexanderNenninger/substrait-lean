### A column no query mentions blocks nothing

A struct column the DuckDB writer has no SQL form for, a `map` column of a Delta table, a zoned timestamp or an unsigned integer failed every plan over their table, also where no query read them (`SELECT d, e, d + e FROM t`, `DeltaSource(...).pipe(agg)`). Such a column is left out of the plan when the transformation and the conditions never mention it. A query that reads it still refuses, now naming the column: `column 'm' of 'orders': type map<…> is not supported`.

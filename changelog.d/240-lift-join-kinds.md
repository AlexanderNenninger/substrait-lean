### The SQL lift refuses joins it would have read wrongly

The sqllogictest replay found queries the SQL lift read wrongly (#240). It now refuses them instead:
- **`ASOF JOIN` and `POSITIONAL JOIN`:** the lift read these as the inner join of their `ON`, or as a cross join. An ASOF join keeps each left row's latest match; a POSITIONAL join pairs rows by position.
- **`t.*` with `JOIN … USING`:** SQLGlot leaves the `USING` columns out of the right table's `t.*`, where DuckDB keeps them. `SELECT *` and listed columns still work.
- **Ordering comparisons (`<`, `<=`, `>`, `>=`) of structs and lists:** DuckDB orders them field by field, with NULLs last, and the model's order differs. Equality still works.

### The SQL lift refuses joins it would have read wrongly

The sqllogictest replay found queries the SQL lift read wrongly (#240). It now refuses them instead:
- **`ASOF JOIN` and `POSITIONAL JOIN`:** the lift read these as the inner join of their `ON`, or as a cross join. An ASOF join keeps each left row's latest match; a POSITIONAL join pairs rows by position.
- **`t.*` with `JOIN … USING`:** SQLGlot leaves the `USING` columns out of the right table's `t.*`, where DuckDB keeps them. `SELECT *` and listed columns still work.
- **Ordering comparisons (`<`, `<=`, `>`, `>=`) of structs:** DuckDB orders them field by field, with NULLs last, and the model's order differs. Lists still compare as DuckDB's, and equality still works.

Other queries the replay found read wrongly are refused or fixed too:
- **Clauses SQLGlot attaches to a table:** `TABLESAMPLE`, `PIVOT`, and the comma joins of a FROM-first query (`FROM a, b SELECT …`) are now refused. The lift used to read only the table and drop them.
- **Numbers with an underscore not between two digits** (`1__2`, `1._5`): DuckDB reads such an underscore as the start of an alias, SQLGlot as a digit separator (upstream/LEDGER.md SG-4). These are refused.
- **A constant that doesn't fit its cast's type** (`200::TINYINT`, `12.5::DECIMAL(2,1)`): the lift now writes the cast instead of an out-of-range literal. A string read as a decimal is read exactly, so `'1e38'::DECIMAL(38,0)` no longer goes through a double.
- **INTERVAL output columns:** these are refused, because the model holds intervals as microseconds while DuckDB keeps months and days apart.
- **Casts to the `NULL` type:** refused.

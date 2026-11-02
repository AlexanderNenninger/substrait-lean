### The SQL lift reads strings

The SQL lift now reads strings (#240): `length`, `substring`/`substr` (from
1; a negative start counts from the end), `trim`/`ltrim`/`rtrim` (spaces,
or the characters given), `strpos`/`instr`/`position`, `contains`,
`starts_with`, `ends_with`, `prefix`, `suffix`, `LIKE`/`ILIKE` and their
`NOT`, `||`, `concat` (which leaves NULLs out), `replace`, `repeat`, `left`,
`upper` and `lower`. A LIKE pattern must be a constant without a backslash:
DuckDB's LIKE has no escape character, and the model's has one. `reverse`
is refused, because DuckDB reverses grapheme clusters.

### Lists in DuckDB SQL: literals, indexing, UNNEST

The SQL lift reads DuckDB's list literals (`[1, 2, 3]`, nested ones too),
`l[i]` with a constant index (from 1, from the end for a negative `i`, NULL for
`0` and out of range), and `UNNEST(l)` in the select list (one row per
element, none for a NULL or empty list) (#348). Lean's results match DuckDB's.
DuckDB's SQL writer has no lists yet (#94), so these plans are checked against
DuckDB's own result but not run back; the sqllogictest ledgers now count such
agreements apart ("Oracle A only"). Lists of computed elements, of DECIMALs,
slices and an untyped `[]` are refused with a reason.

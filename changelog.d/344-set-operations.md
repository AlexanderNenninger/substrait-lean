### Set operations in SQL

DuckDB SQL with `UNION`, `EXCEPT` and `INTERSECT`, each with or without `ALL`,
now verifies, in subqueries and CTEs too, with `ORDER BY` and `LIMIT` over the
whole operation (#344). The branches meet at DuckDB's common column types, and
take the first branch's names. NULLs count as equal, and with `ALL`, `m` and
`n` copies of a row leave `min(m, n)` (`INTERSECT ALL`) or `max(m − n, 0)`
(`EXCEPT ALL`), as in DuckDB. DuckDB's `TABLE t` shorthand, which SQLGlot does
not parse, is written out as `SELECT * FROM t` first. In the sqllogictest
replay, the `setops` area went from 18 agreeing queries to 79, none disagreeing.
`UNION BY NAME` is still refused, and without keys on its inputs a report calls
`INTERSECT ALL`/`EXCEPT ALL` undetermined.

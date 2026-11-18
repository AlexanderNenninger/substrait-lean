### Correlated `EXISTS` and `NOT EXISTS` lift

A correlated `[NOT] EXISTS` that is a conjunct of `WHERE` lifts as a semi (anti) join of the outer relation
with the subquery's `FROM`, on the conjuncts that read the outer query's columns; the others filter the
subquery's side. Names resolve innermost first. The shapes that stay refused name what to write: a `GROUP BY`,
`HAVING`, `DISTINCT`, `ORDER BY`, `LIMIT` or a computed select list in the subquery, an `EXISTS` under
`OR`, `CASE` or `NOT (… AND …)` or in the select list, an outer reference in a join's `ON` or in a nested
subquery. Correlated `IN` and `NOT IN` follow
([#345](https://github.com/AlexanderNenninger/substrait-lean/issues/345), [#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

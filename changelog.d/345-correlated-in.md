### Correlated `IN` and `NOT IN` lift

`x [NOT] IN (SELECT k FROM r WHERE …)` that reads the outer query's columns, as a conjunct of `WHERE`, lifts as a
semi (anti) join. `IN` is a semi join on `x = k AND p`; `NOT IN` an anti join on
`p AND (x = k OR x IS NULL OR k IS NULL)`, so a NULL needle or a NULL in the subquery's column keeps SQL's three-valued
answer (a row stays only if no row of the subquery with `p` TRUE equals `x` or makes the comparison NULL; an empty
result keeps it, also for a NULL `x`). The subquery's shapes are those of correlated `EXISTS`; one that reads the
outer query in its select list, returns two columns or sits under `OR` or in the select list is refused by name
([#345](https://github.com/AlexanderNenninger/substrait-lean/issues/345), [#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

### Preconditions that relate columns are used in proofs (#597)

A precondition of any shape, such as the implication
`(_.a <= 0) | (_.b < 0)`, is now kept whole as a fact about each row. A
postcondition that restates it is proved wherever the plan carries it
through: projections that keep its columns, filters, sorts, limits, joins
and `UNION ALL`s whose inputs all have it. Under a filter or in a `CASE`
branch, the disjuncts that cannot be TRUE drop out and the rest narrows the
columns: under `t.filter(_.a > 0)` the implication gives `b <= -1`, also
when `a` or `b` may be NULL. Before, these postconditions were reported as
"TRUE or FALSE". Filter conditions are kept whole the same way. Steps 1 and
2 of #597; see `docs/guide.md`.

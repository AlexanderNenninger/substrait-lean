### Plans with `NOT IN` subqueries and decimals are written

A plan with DECIMAL arithmetic is written for the engines only if it reads
back as the same plan. A `NOT IN (subquery)`, or a `CASE` of several
branches, grew on every reading, so such a plan stopped at "this decimal
arithmetic cannot be written for the engines yet" (#238, TPC-H Q16's
shape). It is written now.

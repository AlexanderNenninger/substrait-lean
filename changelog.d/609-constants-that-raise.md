### Constants that raise raise for the whole plan (#609)

A constant subexpression that raises, such as `1 // 0 = 1` in a later
`CASE WHEN`, now makes `verify` report the plan as raising, whatever the data
and whichever branch the rows take. DuckDB evaluates a `CASE`'s constant
conditions when it plans the query, so such a plan raised on any data, an
empty table included, though `verify` had proved it. The issue is flagged
`constant`, and the report says no precondition rules it out (D21). This
changes the reference and ships in a minor version bump (D17).

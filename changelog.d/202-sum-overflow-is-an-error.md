### An integer `SUM` that may overflow makes a report unproved

`verify` now treats "SUM overflow" like every other error: where a group's
integer sum may leave 64 bits, `Report.proved` is false and `@sv.transform`
refuses the transformation. Sverify rules the overflow out where the plan
bounds a group's rows (a `VALUES` list, a `FETCH` count, an aggregate without
groups) and `requires` bounds the column; row bounds on tables are #219. The
job still checks the sum while it runs. A window `SUM` or `AVG` whose frame
may hold both `+inf` and `-inf` is now reported as a domain error, as the
grouped one is (#257).

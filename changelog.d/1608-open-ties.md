### The written SQL leaves ties open, as the reference does

Under the default observation (`rows="multiset"`), `report.to_sql` and
`node.to_sql` no longer number rows by `rowid` to break ties as Lean's list
order does. A sort, a `LIMIT` and a window below it use the sort keys alone;
the result is ordered only where the plan's last sort orders it. Plans with
open ties no longer return `Rel.eval`'s rows on every run unless the report is
`reproducible` or `rows="sequence"` asks for them. On 3 million rows in
DuckDB the survey's window queries run 1.8 to 2.1x faster
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

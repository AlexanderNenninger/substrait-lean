### A time of day plus an interval, and truncated

`t.ts.time() + ibis.interval(hours=1)` and `t.ts.time().truncate("h")` now
verify, and run on DuckDB. A time of day plus a constant interval wraps around
midnight both ways, as DuckDB computes it (`TIME '23:30' + INTERVAL 1 HOUR` is
`00:30`); an interval with months is refused. Truncation to an hour, minute,
second or millisecond is a floor of the microseconds. The SQL lift reads
DuckDB's `TIME ± INTERVAL` too. Other engines refuse both until #271
([#507](https://github.com/AlexanderNenninger/substrait-lean/issues/507)).

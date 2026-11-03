### Benchmark catalogue refreshed for 0.4.0

The catalogue's 54 benchmark queries were probed again on 0.4.0. 53 are accepted and 53 now have a contract, of which 46 are proved and 49 run as verified SQL on DuckDB (#229). New contracts: TPC-DS q27 and q36 (ROLLUP lifts since #306) and H2O groupby q9 (`corr`). A query written in SQL now states its contract as SQL conditions.

TPC-H q11, q14 and q20 state row caps from the specification's largest scale factor. Each query still short of proved or verified SQL says why in its TOML, with the issue that would close it: SUMs bounded by row caps (#470), RANK over a ROLLUP (#471), keys through a FULL JOIN (#472) and ROW_NUMBER filters projected past their ties (#473).

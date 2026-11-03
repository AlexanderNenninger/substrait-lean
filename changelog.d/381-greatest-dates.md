### GREATEST and LEAST of date and timestamp constants run as dates again

`LEAST(DATE '1992-01-01', DATE '1991-01-01')` and its timestamp counterpart returned the integer code of the result on DuckDB (`7670`, `662693025000000`), whenever every argument was a constant (#381, a regression of #355). The plan Lean writes back now writes two constants in the call's own kind, as it does elsewhere, so they are dates and timestamps to the engines. Lean's own results were right throughout.

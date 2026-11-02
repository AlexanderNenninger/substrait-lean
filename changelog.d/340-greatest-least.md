### GREATEST and LEAST check in linear time

`GREATEST(a, b, c, …)` and `LEAST(…)` used to be read as a chain of conditionals, each of which copied the one before. With ten arguments, the checker ran for minutes, and a plan written back held thousands of copies of each argument (#340). They're now one operation per pair, `BinFn.greatest`/`least`, which `Expr.eval_greatest` proves is the conditional it replaces. Thirty arguments check in well under a second.

The contract checker keeps its precision. `GREATEST(x, 0)` is still known to be at least 0, and Ibis's `clip` to stay within its bounds; `pickAbs` is proved sound. Written plans carry `greatest`/`least` as single calls, run natively:
- DuckDB, Spark and DataFusion: their own `GREATEST`/`LEAST`, which skip NULLs;
- Snowflake: `GREATEST_IGNORE_NULLS`;
- Polars: the same comparison as before, now one step per pair.

Greatest and least of lists are written as the conditional, as before.

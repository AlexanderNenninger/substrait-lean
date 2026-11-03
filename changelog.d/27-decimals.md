### Decimals

`DECIMAL(p, s)` columns, literals and arithmetic are verified, in Ibis and in
SQL (#27, #67). The reference computes them exactly: `+` and `-` at the
larger scale, `*` at the sum of the scales, and an overflow of the precision
is an error, which `verify` rules out from the columns' declared precision.
Casts to a smaller scale round half away from zero, to an integer truncate,
and to and from doubles round once. `SUM`, `MIN`, `MAX` and `AVG` work in
groups and windows; `AVG` is `DECIMAL(p + 4, s + 4)`, rounded half away from
zero. Division of decimals is refused. DuckDB runs decimal plans and
compensates where its own types or rounding differ
([engine profiles](../docs/engine-profiles.md)); Polars, Spark and Snowflake
refuse them for now.

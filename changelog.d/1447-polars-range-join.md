### Polars runs a join on a range comparison as a range join

A join with no equality between the two sides, whose condition compares a column of one side with one of the other (`t.ts >= u.start`, `t.a > u.b`), now runs on Polars as a streaming range join (`join_where`) in place of a cross join and a filter. The rows are the same ([#1447](https://github.com/AlexanderNenninger/substrait-lean/issues/1447)).

On Polars, a keyless join whose condition has a range comparison may now return where it raised before: when the raising pair fails the range comparison, it is in no result the reference allows (D16).

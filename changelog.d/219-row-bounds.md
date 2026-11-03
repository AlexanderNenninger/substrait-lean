### Row-count bounds prove integer SUMs fit

`sv.rows(at_most=N)` states how many rows an input has (#219). It is checked
on the data at call time and on every refresh, or proved from the record
counts of a Delta or Iceberg table's files. Lean carries the bound through
filters, joins (a join on a `unique` key keeps the left side's rows), unions,
limits and aggregates (`Rel.maxRows_sound`), and an integer `SUM` whose values
and rows keep it within 64 bits is no longer reported as "SUM overflow"
(`Rel.issuesR_sound`). `Report.rows` bounds the output's rows, the SUM hint
names the row bound that proves the sum fits, and `sv.rows` in `ensures` is
proved from the inputs.

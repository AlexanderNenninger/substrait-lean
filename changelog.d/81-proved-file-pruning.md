### Proved file pruning: Iceberg, string bounds, NaN and implied predicates

`IcebergSource` takes `where=` as `DeltaSource` does: the source is the rows
on which the condition is TRUE, and snapshots, native scans and appends read
only the data files whose statistics do not rule it out. Both sources now
also skip files by string bounds, which Delta and Iceberg may cut to
prefixes, for `=`, `<`, `<=`, `>`, `>=` and `IN` of a string column and a
literal. `SubstraitLean/Pruning.lean` proves the criterion against the exact
statistics semantics, with NULL counts, NaN left out of double bounds and
truncated string bounds, and that every plan linear in the source gives the
same result from the files kept (`Rel.eval_pruned`). For `amount * 2 > 100`,
pyarrow's statistics pushdown reads every file and sverify skips those with
`amount <= 50` (`test_iceberg_where_skips_files_the_reader_would_scan`).

A node now also prunes from predicates its view implies on a source and the
query does not state. With `o.ts >= c.since` in a join of orders and
customers, and `since >= DATE '2026-01-01'` among the customers'
preconditions, the orders source reads only orders from 2026 on and skips
older files. Lean derives the predicate from the preconditions, Delta CHECK
constraints and source conditions, and proves that the view's result is the
same (`Rel.need_eval` in `SubstraitLean/Implied.lean`). `Report.implied`
lists the predicates a transformation implies on its inputs
([#81](https://github.com/AlexanderNenninger/substrait-lean/issues/81)).

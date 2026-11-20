### Seven proved rewrites run by default

`Report.run` now runs the rewritten plan where one of seven proved rewrites
applies and the run checked your preconditions on the data
([#1787](https://github.com/AlexanderNenninger/substrait-lean/issues/1787),
ruling 150): an implied filter, a filter the contract rules out, `DISTINCT`
or `GROUP BY` on a key, `fn(DISTINCT key)`, and a join to a keyed table none
of whose columns the query reads. The engine gets other SQL for those plans,
and under `rows="multiset"` the rows may come back in another order.
`run(check_requires=False)`, `run(optimize=False)` and `Report.to_sql` keep
the plan as written; `to_sql(optimize=True)` writes the rewrite, for data you
know meets the preconditions. The name `optimize` is provisional. The report's
`run_gate` says when the checker kept the plan as written. The bench and the
rules that stay off are in `docs/optimizations.md`, "The gate".

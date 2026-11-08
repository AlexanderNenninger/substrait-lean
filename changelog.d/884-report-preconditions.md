### Breaking: a call's preconditions come back on its report

A contracted transform's call reports how it established each precondition
on a bound input (from the schema, from table metadata, or on the data) in
`Report.preconditions`, a list of `Discharged`, on the call's own report
(`transform.report`). A refresh reports its own in
`StageRefresh.preconditions`, as before
([#884](https://github.com/AlexanderNenninger/substrait-lean/issues/884)).

Moves:

- `ContractedTransform.last_preconditions`, deprecated since 0.6, is removed.
  Read `transform.report.preconditions`, or a refresh's
  `StageRefresh.preconditions`. The transform no longer keeps the last
  call's preconditions as state of its own, which a later call overwrote.

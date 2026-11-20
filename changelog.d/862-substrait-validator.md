### Exported plans pass Substrait's validator

`report.to_substrait()` writes plans `substrait-validator` accepts: a
projection that only reorders columns becomes its input's output mapping, a
typed NULL is nullable, a constant table's values have its columns' types, an
`if_then`'s NULL or decimal constant takes its other branches' type, and the
plan declares the contract message it carries (`expected_type_urls`). A
precondition on a text column (`reverse` needs ASCII) no longer fails the
export, and `from_substrait` checks it again. Exports ask the checker's
transfer check once per process, about six times faster. CI validates every
coverage case and catalogue query with the validator and records the result
in a ledger ([#862](https://github.com/AlexanderNenninger/substrait-lean/issues/862)).

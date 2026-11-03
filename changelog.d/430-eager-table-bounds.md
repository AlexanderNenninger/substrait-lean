### Inferred bounds on eager tables

`@sv.transform` on an eager table (an `ibis.memtable`, or any plain Ibis
expression that is not a contracted result) now infers the bounds that rule
out overflow, checks them on the table's data, and proves the contract, as
`sv.verify` does. Hints name the bound as a `requires` of the parameter
([#430](https://github.com/AlexanderNenninger/substrait-lean/issues/430)).

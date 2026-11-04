### Ibis conditions on SQL transformations

`sv.verify` on a SQL string took only SQL conditions and raised a
`TypeError` on an Ibis one. Its `ensures` and `requires` now take Ibis
conditions too: an Ibis postcondition reads the lifted query's output, and
an Ibis precondition its input table, so a query keeps its contract when it
moves between SQL and Ibis
([#438](https://github.com/AlexanderNenninger/substrait-lean/issues/438)).

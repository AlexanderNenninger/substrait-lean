### A sink recovers from a write that failed after its commit

A `DeltaSink` write that raised after its commit had landed, for example
reading the table's version back while the object store restarted, left
every later refresh of the node failing in the same process until a restart
([#488](https://github.com/AlexanderNenninger/substrait-lean/issues/488)).
The next refresh now finds the epoch the table committed in its transaction
version and writes on from that state, as a restarted job does. A write that
failed before its commit is replayed. This holds for every sink with a
`committed()` that reads the sink back.

### A new connection no longer inherits a dead one's table facts

The metadata facts of a table read from a table format were kept by the
`id` of its connection's backend. Once that connection was gone, a new
connection could get the same `id` and take its facts for its own table of
the same name: a row-count fact then discharged a `rows_per` or `max_rows`
precondition the data broke
([#938](https://github.com/AlexanderNenninger/substrait-lean/pull/938)).
Each entry now holds a weak reference to its backend, and a dead backend's
entries are dropped.

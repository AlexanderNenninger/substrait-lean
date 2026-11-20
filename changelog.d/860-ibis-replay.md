### Ibis's own tests replayed through sverify

`sverify_dev.ibis_replay` runs Ibis 12.0.0's backend tests on DuckDB and
verifies and runs every expression they execute through sverify, against
Ibis's own rows: 431 tests agree, none disagree, and each of the 594 refused
names its issue or why it is refused by design
([#860](https://github.com/AlexanderNenninger/substrait-lean/issues/860)).
The replay found two bugs. Ibis's cast of an integer to a timestamp reads
seconds since the epoch, where sverify read microseconds (fixed in its own
change). A run refused a table with a float32 column the query never reads
when it checked a precondition; the check now reads only the columns the
preconditions read, as SQLGlot finds them.

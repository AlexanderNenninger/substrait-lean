### An Ibis table with a DuckDB ENUM column is refused

Ibis types a DuckDB `ENUM` as `string`, so a plan over an Ibis table bound to
a DuckDB backend was proved under text order, where DuckDB orders an `ENUM` by
declaration position
([#1253](https://github.com/AlexanderNenninger/substrait-lean/issues/1253)).
The DuckDB engine now reads the declared types of the base tables an Ibis
expression scans and refuses `UUID`, `ENUM`, `BIT` and `BIGNUM` columns with
the exit (`CAST(col AS VARCHAR)` in the source query). A plugin may set
`ProfilePlugin.refuse_declared_types` to do the same for its engine.

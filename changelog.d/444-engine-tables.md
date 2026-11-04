### DuckDB and Polars as choice tables

`substrait-check --options` now prints DuckDB's (2.0.0) and Polars's (2.1.0)
choices and how each relates to the reference, option by option, for integer
and double arithmetic, `SUM`, `AVG` and sorts, from their facts in
`characterization/`
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).
A plan's integer `divide` may now state `division_type: TRUNCATE`, which is
what it computes.

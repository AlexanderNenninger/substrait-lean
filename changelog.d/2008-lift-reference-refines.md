### The default semantics' SQL lift is proved against DuckDB

SQL lifted under `semantics="reference"` now uses the proved entries of the
lift's reference table, and Sverify proves that each of them, wherever it gives
a value, gives DuckDB's (`liftReference_refines_duckdb`, D54,
[#2008](https://github.com/AlexanderNenninger/substrait-lean/issues/2008)).
`CAST(DOUBLE AS BIGINT)` stays refused under the reference (D55), now with the
refusal text of the Lean table.

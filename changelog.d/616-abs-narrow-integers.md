### `ABS` of a narrow integer

`verify` no longer crashes on `abs` of an `int8`, `int16` or `int32` column ([#616](https://github.com/AlexanderNenninger/substrait-lean/issues/616)). The model checks `ABS` at the column's width, as DuckDB does (`abs(-128::TINYINT)` raises), and the inferred bound stays within the column's type: `v >= -127` for an `int8`. An inferred bound never reaches `2**63`, and a SQL comparison of a narrow column with a constant that fits it compares the column itself, so such a bound in `requires` is used by the proof.

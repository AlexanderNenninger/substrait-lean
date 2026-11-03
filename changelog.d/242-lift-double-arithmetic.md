### DuckDB's `+`, `-` and `*` of doubles are proved

With `semantics="duckdb"`, the SQL lift now writes `+`, `-` and `*` of
doubles from Lean's generated lift table (#242): `inf - inf`, `-inf + inf`
and `0 * inf` are NaN, as in DuckDB, and the checker proves the template
means what DuckDB computes. Before, these lifted to the reference's
operations, which raise there, so the DuckDB SQL sverify wrote raised a
domain error where DuckDB gives NaN (oracle A, `types/float/nan_arithmetic.test`).

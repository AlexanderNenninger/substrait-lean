### DuckDB's float-to-integer casts come from the proved lowering

DuckDB's `CAST(x AS BIGINT)` of a double rounds halves to even, and the
reference truncates. Sverify's DuckDB SQL now truncates first
(`CAST(CASE WHEN x < 0 THEN CEIL(x) ELSE FLOOR(x) END AS BIGINT)`, and the
same under `TRY_CAST`), from a template the Lean build proves gives the
reference's value (`Lowering.ftoi_agree`, `Lowering.ftoiOrNull_agree`). The
profile states DuckDB's rounding cast, so the two functions leave DuckDB's
list of unproved natives (#2572).

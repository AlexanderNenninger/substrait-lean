### `CAST(decimal AS integer)` and scale-reducing decimal casts in DuckDB SQL

The SQL lift reads `CAST(dec AS BIGINT)` as DuckDB does, rounding half away from zero (the rescale to scale 0, then the exact cast), under `semantics="reference"` and `"duckdb"`. `CAST(dec AS DECIMAL(p, s))` to a smaller scale lifts too. The double case stays refused until the rounding cast lands (#322).

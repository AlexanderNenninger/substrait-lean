### Fixed: Spark's IEEE division by `-0.0`

A division of doubles under `on_division_by_zero` = `IEEE` (what `semantics="duckdb"` asks for) returned the opposite infinity on Spark for a `-0.0` divisor: `1 / -0.0` gave `+inf` where the reference gives `-inf`, in every release since 0.2.0. Spark now writes the plain `/`, so an IEEE division by a zero of either sign raises on Spark (`DIVIDE_BY_ZERO`), as Spark's engine model states; DuckDB SQL with a zero divisor raises there where DuckDB returns `±inf`. Snowflake's division was the plain `/` already.

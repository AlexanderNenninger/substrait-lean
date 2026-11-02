### The SQL lift reads Lean's generated DuckDB lift table

With `semantics="duckdb"`, the SQL lift now writes what Lean's generated lift table says for each construct it covers (#268): `/`, `%` of doubles, `log`, `sign`, `greatest` and `least`, casts between BIGINT and DOUBLE, and `avg` of integers. Lean generates each entry and proves it means what DuckDB computes. `substrait-check --lift-table` exports the table, and the lift reads it from the checker sverify ships with.

The entries state NaN and ±inf exactly, as DuckDB computes them, instead of refusing them or raising:
- `%` of doubles is no longer refused: by zero, or of an infinity, it is NaN.
- `log(0)` is `-inf`, and `log` of a negative is NaN.
- `inf / inf` is NaN.

A contract that NaN or an infinity would break fails to prove, and one they can't break still proves. `avg` of integers is the exact sum divided by the count, in doubles, as DuckDB computes it.

The other constructs keep their hand-written rules until their entries are generated. The reference semantics is unchanged.

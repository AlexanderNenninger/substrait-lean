### A window's `MIN`, `MAX` and `QUANTILE_DISC` of doubles may return any zero or NaN of its class (D45)

D45 now covers windows. Over a frame, `MIN`, `MAX` and `QUANTILE_DISC` allow
any member of the selected value's class among the frame's values, or the
class's canonical value, as they do in a group. DuckDB's windowed `MIN` and
`MAX` return either zero by row order (`duckdb-minmax-zero-sign`), and both
are now results the reference allows.

One verdict changes: a plan with a windowed `MIN`, `MAX` or `QUANTILE_DISC`
over an argument that may be a double loses its determinism certificate
(`report.deterministic` is false), and the report names the window function
("keeps any member of a class of doubles"). Over arguments without doubles
nothing changes.

### What DuckDB SQL lifts to is generated and proved

The Lean build now generates, for DuckDB's `/` (of integers and of doubles),
`%` of doubles, `log`, `sign`, `greatest` and `least` (which skip NULLs) and
casts between BIGINT and DOUBLE, and the aggregate `avg` of BIGINTs, the Substrait expression each lifts to under
`semantics="duckdb"` and `"reference"`, and proves it means what DuckDB's
function means (`SubstraitLean/DuckDBSQL.lean`, `LiftSearch.lean`). With
DuckDB's semantics, `±∞` and NaN results are stated exactly, as guarded
constants: `log(0)` is `-∞`, `x % 0.0` is NaN. `substrait-check --lift-table`
prints the table as JSON, for the SQL lift to read; a function the model
cannot state is listed as refused, with the reason (DuckDB's `CAST` of a double
to an integer rounds half to even)
([#268](https://github.com/AlexanderNenninger/substrait-lean/issues/268)).

DuckDB's `avg` of integers sums them exactly before dividing; with DuckDB's
semantics it now lifts to `CAST(sum(x) AS DOUBLE) / count(x)`, proved equal,
where Substrait's `avg` of doubles would round as it sums (values beyond 2⁵³).

### DuckDB's Lean half, a Lake package of its own

DuckDB's functions under its settings, the SQL printer's model and its
soundness, the black boxes and the casts from VARCHAR, its choice table and
the lowering's lemmas move into `engines/duckdb/`, the Lake package
`sverify-duckdb` with modules `Sverify.DuckDB.*`, beside its Python
distribution ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
It builds on the core, the analysis and engines-common alone, and CI checks
that it does. The generated lowering, `Engine.duckdb` and the lift stay in
the root package until the generators move. No theorem changed.

### DuckDB's lowering joins its Lean package

The lowering generator (`generate_lowering`, `Sverify.Engines.LoweringSearch`)
moves into engines-common, and DuckDB's lowering, its generated entries, its
cache and `Engine.duckdb` into `sverify-duckdb`
([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
The package reads `check_generated` itself, and the root passes its own
setting on. The lift stays in the root package until its parser has a
package. No theorem changed.

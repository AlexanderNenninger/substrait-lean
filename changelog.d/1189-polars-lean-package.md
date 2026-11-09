### Polars's Lean half, a Lake package of its own

Polars's table, shims, profile and `Engine` value move into
`engines/polars/`, the Lake package `sverify-polars` with modules
`Sverify.Polars.*`, beside its Python distribution
([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
It builds on the core, the analysis and engines-common alone, and CI checks
that it does. No theorem changed.

### Spark's Lean half, a Lake package of its own

Spark's table, shims, profile and `Engine` value move into `engines/spark/`,
the Lake package `sverify-spark` with modules `Sverify.Spark.*`, beside its
Python distribution
([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
It builds on the core, the analysis and engines-common alone, and CI checks
that it does; it no longer imports Polars's shims. No theorem changed.

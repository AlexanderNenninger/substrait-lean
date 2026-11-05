### DuckDB's statistical aggregates are proved

DuckDB's `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` (Welford's update with
Chan's merge) are proved to have the properties the reference allows, so
their `stat_algo` row rests on a proof
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444),
[docs/float-bounds.md](docs/float-bounds.md)). Polars's stay tested.

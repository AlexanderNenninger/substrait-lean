### Polars runs every query in memory

Polars 2.1.0's `collect()` streams a lazy query by default, and its streaming
engine adds doubles with other algorithms than the in-memory one the Polars
facts were probed with (`characterization/polars/facts/polars-sum-float.json`).
Sverify now runs each Polars query on the in-memory engine, whatever
`POLARS_ENGINE_AFFINITY`, `pl.Config.set_engine_affinity`,
`POLARS_FORCE_STREAMING` or `POLARS_AUTO_STREAMING` say; the last two are
hidden from Polars while the query runs. A Polars `LazyFrame` given as a
source is collected in memory too
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

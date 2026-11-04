### Polars runs every query on the streaming engine

Sverify now runs each Polars query on Polars's streaming engine, named
explicitly, so `POLARS_ENGINE_AFFINITY`, `pl.Config.set_engine_affinity`,
`POLARS_FORCE_STREAMING` and `POLARS_AUTO_STREAMING` no longer choose the
engine. A Polars `LazyFrame` given as a source is collected the same way.
Operators the streaming engine lacks still run on the in-memory engine inside
the streaming plan; `sverify.polars_engine.streaming_fallbacks` lists them
for a query
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

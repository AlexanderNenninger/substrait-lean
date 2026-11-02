### The last of DataFusion's SQL path is gone

sverify no longer monkey-patches Ibis's DataFusion SQL compiler: the two
patches (sub-second interval literals, integer `//`) changed Ibis for every
user of Ibis-on-DataFusion and served only the internal
`sverify.engine.to_sql`, which is removed as well. The one `to_sql` left is
`sverify.engines.to_sql`, which writes SQL from a checked plan. The query
catalogue runs each query on DuckDB itself rather than DataFusion
(`status.json` records it as `native`), and no longer asks DataFusion's SQL
planner whether a query plans.

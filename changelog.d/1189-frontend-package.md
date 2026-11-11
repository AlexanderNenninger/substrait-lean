### The frontend, a Lean package of its own

The Substrait JSON parser (`Parse`) and the builders of Substrait's JSON
(`SubstraitJson`) move into `frontend/`, the Lake package `sverify-frontend`
with modules `Sverify.Frontend.*`, which builds on the core and the analysis
alone ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
The lift from DuckDB's SQL (its generator, hints, cache and generated
entries) joins `sverify-duckdb`, which imports the frontend. DuckDB's Lean
half is now all in its package. No theorem changed.

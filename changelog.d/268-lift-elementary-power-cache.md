### DuckDB's elementary functions and power lift exactly, and the lift has a cache

With `semantics="duckdb"`, `sqrt`, `exp`, `ln`, `log`/`log10`, `log2`, the
trigonometric functions and `power` now lift to what DuckDB computes, NaN and
`±∞` included (`sqrt(-1)` and `asin(2)` are NaN, `ln(0)` is `-∞`, a negative
base to a fractional power is NaN), each proved
([#268](https://github.com/AlexanderNenninger/substrait-lean/issues/268)). The
lift generator keeps a cache of the templates it found
(`SubstraitLean/LiftCache.lean`, regenerated with `substrait-check
--lift-cache`), tried first on the next build: a build with the cache takes
15 s where a search from scratch takes about 3 minutes. A template the search
does not reach can be seeded by hand there; it is still proved by the kernel.

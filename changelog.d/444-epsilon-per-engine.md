### The float tolerance per engine

`--contract` now gives each double output column a bound per engine
(`"epsilon_by_engine"`). The bound carries the summation order's share and
each engine's own per-operation error through `+ − × /` from the ranges the
preconditions give: Polars's division by a literal is within 3u of IEEE's
quotient, and its `log10`, `log2` and `log(b)` within 2.1 ulp; DuckDB's
`log(b, x)` within 1.4 ulp; `+ − × /` and `sqrt` are correctly rounded on
both. Lean does not prove these bounds yet
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

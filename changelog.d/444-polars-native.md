### Polars plans stream, with native expressions

The Polars engine now computes integer `POWER`, month arithmetic and
`date_trunc` of dates, `GREATEST` and `LEAST`, double sort, group and join
keys, and the aggregates `COUNT`, `MIN`, `MAX`, `BIT_AND`, `BIT_OR`,
`BIT_XOR`, `VARIANCE`, `STDDEV` and their `DISTINCT` forms as Polars
expressions, where it ran Python and numpy on each batch before, so these
plans run fully on Polars's streaming engine. A test checks every plan the
Polars tests run: a node on the in-memory engine fails it unless
`polars_engine.ALLOWED_FALLBACKS` lists it (`ARRAY_AGG`'s ordered list,
window frames). `Report.run(..., streaming="require")` refuses a plan with
such a node, and a routed run records them in `Route.fallbacks`.

Double `/` is Polars's own: by a constant it goes through the reciprocal and
is within 2 ulps (PL-3, from #608), and a subnormal divisor is refused on the
data. numpy, imported only when needed, keeps `%` of doubles (C's `fmod`)
and `ROUND(x, d)`'s division by `10^d` exact. `power(-inf, 0.5)` is `+inf`
and a difference of zeros the one zero, where Polars gives NaN and `-0.0`
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

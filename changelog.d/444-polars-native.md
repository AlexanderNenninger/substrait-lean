### Polars computes more natively, with numpy for double division only

The Polars engine now computes integer `POWER`, month arithmetic and
`date_trunc` of dates, double sort, group and join keys, and the aggregates
`COUNT`, `MIN`, `MAX`, `BIT_AND`, `BIT_OR`, `BIT_XOR`, `VARIANCE`, `STDDEV`
and `ARRAY_AGG` as Polars expressions, where it ran Python and numpy on each
batch before. numpy is imported only for double `/` and `%`: Polars divides a
column by a constant through its reciprocal, so `49.0 / 49.0` is
`0.9999999999999999` there (`upstream`: PL-3, fact
`polars-double-scalar-divisor`). A double `+` or `-` is now `0.0` where Polars
rewrites `0.0 - x` as `-x` (fact `polars-zero-sign`)
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

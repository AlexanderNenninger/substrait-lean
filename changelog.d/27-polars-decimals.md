### Polars runs decimal plans

`engine="polars"` runs plans over `DECIMAL` columns, which it used to refuse
("unsupported column type"). Values keep the plan's `DECIMAL(p, s)`, and the
translation computes what Polars rounds differently: a product at the sum of
the scales, a smaller scale and an `AVG` half away from zero, an empty `SUM`
as NULL ([#27](https://github.com/AlexanderNenninger/substrait-lean/issues/27),
[engine-profiles.md](docs/engine-profiles.md#decimals-on-polars)). The 22
TPC-H queries, 8 TPC-DS queries and 10 finance queries of the catalogue now
run on Polars. A cast of a double to a decimal of more than 22 places is
refused there.

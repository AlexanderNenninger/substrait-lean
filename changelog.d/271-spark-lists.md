### Spark runs lists

Spark now runs `unnest()`, list literals, list elements and lengths, and an unordered `collect()`
([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)): `posexplode` in a lateral
subquery, `array`, `try_element_at`, `cardinality` and `collect_list`, which gives NULL where the
reference does for no values. An ordered `collect()` stays refused, since `collect_list` has no
`ORDER BY`.

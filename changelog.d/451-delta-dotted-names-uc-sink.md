### Delta tables with dots in their names, and `uc://` sinks

A `DeltaSource` or `DeltaSink` whose path ends in a name with dots
(`.../homelab.metrics.orders`, or `uc://homelab.metrics.host_minute`) got a
default name with dots, which the DuckDB engine read as catalog.schema.table,
so the first refresh failed
([#451](https://github.com/AlexanderNenninger/substrait-lean/issues/451)).
The default name now replaces the dots with underscores
(`homelab_metrics_orders`), and for `uc://catalog.schema.table` it is the
table's name (`host_minute`).

`DeltaSink("uc://…")` no longer hangs in delta-rs 1.6.6's
`DeltaTable.is_deltatable`: it opens the table, and raises a `ValueError`
saying to register the table first when Unity Catalog doesn't have it, since
a sink can't create a table through the catalog. The `DeltaSource` docs note
that delta-rs takes the `unity_*` options in lowercase and that a MinIO
endpoint goes in the same options as the catalog's.

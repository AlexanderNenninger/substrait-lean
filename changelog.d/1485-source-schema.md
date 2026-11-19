### `DeltaSource(uri, schema=...)` and `IcebergSource(catalog, id, schema=...)`

With a declared schema, building a node and `sverify check` prove a transform without opening the table: no lake credentials or network on a pull request, and no failure for a table that does not exist yet. Every refresh reads the table's schema and raises `SchemaError` naming the differences when it is not the declared one (#1485, 18).

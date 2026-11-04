### `uc://` sinks tell a registered table without a Delta log apart

`DeltaSink("uc://…")` on a table Unity Catalog has registered, but whose
storage location has no `_delta_log/` yet, said the table was missing from
the catalog and to register it, which it already was
([#512](https://github.com/AlexanderNenninger/substrait-lean/issues/512)).
The sink now says the location has no Delta table yet, with delta-rs's
reason, and that the first version must be written there (for example with
`write_deltalake` and the catalog's READ_WRITE keys). The catalog's
`TABLE_NOT_FOUND` and `SCHEMA_NOT_FOUND` keep the message to register the
table.

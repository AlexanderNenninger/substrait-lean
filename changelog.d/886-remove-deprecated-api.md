### The deprecated names are gone

1.0 keeps no deprecation alias ([#886](https://github.com/AlexanderNenninger/substrait-lean/issues/886), part of [#2081](https://github.com/AlexanderNenninger/substrait-lean/issues/2081)). Each removal has a replacement:

- `Connection.arrow`: read a table with `con.get(name)` or `con.rows(name)`, write one with `con.put(name, table)`.
- `Connection.ibis`: `con.table(name).get_backend()` is the same Ibis backend.
- `ContractedTransform.last_report` and `SQLStep.last_report`: read `.report`.
- `DeltaSource.hi_slack` and `IcebergSource.hi_slack`: internal, no replacement.
- `sverify.errors.Unsupported` and `sverify.errors.NotIncremental`: `UnsupportedError` and `NotIncrementalError`.
- `sverify.contracts.InferredPreconditionWarning`: `sverify.errors.InferredWarning`.
- `deterministic=` of `Report.run` and `routes.choose`: `reproducible=sv.equivalent()`.
- `StaticSource(table, version)`, and `StaticSource` and `sverify.testing.source` without `name=`: write `StaticSource(table, name=..., version=...)`; `name=` is required.
- The environment variables `SVERIFY_CHECK` and `SVERIFY_SPILL_DIRECTORY`: set `SVERIFY_CHECKER` and `SVERIFY_TEMP_DIRECTORY`.

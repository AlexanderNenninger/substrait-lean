### Breaking: deprecated aliases are removed (#2081, #1288)

A name that warned with a `DeprecationWarning` since 0.x is gone, and the old
form raises. `docs/stability.md` states the 1.0 policy: a renamed or removed
name is not kept as an alias.

| Removed | Write instead |
| --- | --- |
| `sverify.Changes` | `sverify.io.Changes` |
| `sverify.from_substrait(...)` | `sverify.Report.from_substrait(...)` |
| `sverify.io.FlightLog` | `sverify.testing.FlightLog` |
| `Sink.committed()`, and a sink that overrides it | `Sink.contract(version=None)`; override `contract` |
| `Sink.view`, `SinkChange.native` | none: they were internal |
| `IcebergSink.create_options_ignored` | none: it was internal |
| `DeltaSink.maintain(vacuum=)` | `maintain(vacuum_retention=)` |
| `IcebergSink.maintain(expire=)` | `maintain(snapshot_retention=)` |
| `FlightSource(token=)` | `FlightSource(secret="env:NAME")` |
| `run_sharded(float_order="any")` | `run_sharded(reproducible=sv.equivalent(floats="plan"))` |
| `sv.sql(query, as_=...)` | `sv.sql(query, name=...)` |
| `arrives_within(col, days=, hours=, minutes=, seconds=)` | `arrives_within(col, within)`, a `timedelta` or ISO 8601 duration |
| `rows_per(["a", "b"], 3)` | `rows_per("a", "b", at_most=3)` |
| `SVERIFY_PREBUILT_CHECK` | `SVERIFY_PREBUILT_CHECKER` |

The remaining aliases (`Report`'s internal names, `errors.Unsupported`,
`engine.Connection.arrow`, the environment variables of the checker and the
spill directory, and others) go in follow-up changes, since open pull requests
touch their files.

### One definition of the public API, and `sverify.types` (#886)

The public API is the names in the `__all__` of nine modules and the
members without an underscore of the classes among them
([`docs/stability.md`](docs/stability.md#the-python-api)). The API reference
lists each of them, and `tests/test_public_api.py` holds the two equal.

- `sverify.types` is new: the types a public name returns or holds, for
  annotations and `isinstance`. These are the conditions (`Unique`, `Key`,
  `References`, `MaxRows`, `RowsPer`, `ArrivesWithin`, `Approx`,
  `PlannedCondition`), what a report holds (`Issue`, `Needed`,
  `CheckedCondition`, `Discharged`, `Counterexample`, `Observation`,
  `Within`, `Route`, `DialectDifference`), what a refresh returns (`Refresh`,
  `StageRefresh`, `RefreshReport`, `SourceRefresh`, `QuarantineReport`,
  `RetentionReport`, `Status`, `NodeStatus`, `Group`) and `SQLStep`.
  `import sverify` does not import it.
- `sverify.io` exports `Fact` and `Stored`, and `sverify.engines` exports
  `Native` (its members outside the 1.x promise for now) and `Sharded`.
- `ODCS_VERSION`, `SPEC_VERSION`, `FACET_FORMAT` and `FACET_SCHEMA_URL`
  leave their modules' `__all__`. They stay importable, and each value is in
  what sverify writes (the ODCS `apiVersion`, the events' `schemaURL`, the
  `sverify_contract` facet).
- The reference gains the condition constructors, `ContractedTransform`,
  `Verdict`, `io.FlightSource`, the credentials (`io.Secret`, `Resolver`,
  `set_resolver`, `CredentialUse`), `testing.LeanRaised`, and the errors
  and warnings it was missing.

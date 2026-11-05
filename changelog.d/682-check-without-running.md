### Reading a contract's proof without running it

For tools that read a proof, such as an editor, a CI step or dbt
([guide](docs/guide.md#checking-without-running), #682):

- `ContractedTransform.check(**schemas)` proves a transform's contract for
  input schemas and returns the `Report`. It raises no `VerificationError`
  and reads no data. `sv.ContractedTransform` is exported, the type
  `@sv.transform` returns.
- `Report.route(engine)` gives the route a run would take and the plan's
  class there (exact, observed, shim or refused), without running it.
- `Report.inputs` gives the schemas of the input tables.
- `CheckedCondition.message`, `Issue.message`, `Issue.assumption` and
  `Report.notes` give the lines `str(report)` prints.
- `Issue.suggested` gives the preconditions that rule an issue out, per
  table, as data.
- The `SVERIFY_COUNTEREXAMPLES` environment variable sets the counterexample
  budget of `sv.verify`, transform calls and `check`; 0 skips the search.
  The default stays 200.

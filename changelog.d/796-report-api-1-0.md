### Breaking: `Report` before 1.0: one record for needed preconditions, internal fields, `reproducible=` (1.0 API review B1, B4, B5, E1, F6)

From the 1.0 API review (`api-review/PROPOSAL.md`). Every released name
below still works in this release with a `DeprecationWarning`, and goes in
the next.

One record for the preconditions a proof needs (B1):

- `Needed` gains `condition`, the precondition ready for `requires=` (an
  Ibis deferred for an Ibis transform, a SQL string for a SQL one), and
  `text`, the precondition in words with where it comes from and the fixes.
- `report.suggested_requires` is the whole `requires=` mapping: the stated
  preconditions and the inferred ones, ready to pass to `verify` again or to
  paste into a decorator.
- `Issue.needs` is a list of `Needed`, the preconditions that rule the issue
  out. `Issue.suggested` warns; the labels `Issue.needs` used to hold are
  internal.
- `report.suggestions` maps each unproved postcondition's label to a list of
  `Needed`. It used to map it to labels per table.
- `report.needed`, `Report.needs_text()` and `needs_lines()` warn: read
  `report.needs`. The report JSON keeps its keys.

Internal fields (B4, E1):

- `Report` keeps public `requires`, `ensures`, `facts`, `not_null`,
  `deterministic`, `issues`, `assumed`, `rows`, `semantics`, `observation`,
  `routes`, `output`, `ties`, `inputs` and `internal_plan`, with the
  properties `verdict`, `proved`, `unproved`, `needs`, `errors`, `notes`,
  `suggestions` and `suggested_requires`. Its other fields (`guard_free`,
  `unchecked`, `optimized`, `rewrites`, `inferred`, `implied`, `params`,
  `hints`, `tie_places`, `floats_on`, `epsilon`, `depends`, `transfer`,
  `dialect`, …) have an underscore; the old names warn. `report.plan` is
  `report.internal_plan`, as on a node. `str(report)` and `report.to_json()`
  say what they held. The constructor is internal.
- The sinks' `view` and `keeps_retired`, `IcebergSink.create_options_ignored`,
  the sources' `hi_slack` and `SinkChange.native` have an underscore; the
  old names warn. A custom sink still says `keeps_retired = True`.
- `FlightLog` is `sverify.testing.FlightLog`; `sverify.io.FlightLog` warns.

`reproducible=` as the one knob (B5, F6):

- `Report.run(deterministic=True)` and `routes.choose(deterministic=True)`
  warn: write `reproducible=sv.equivalent()`. `report.deterministic` stays
  as the fact.
- On Spark, `Report.run` and a stored node's refresh pass a proved report's
  `deterministic` to the SQL writer, so a window with no ties (a key on its
  partition and order columns) runs there; it used to be refused.
- `sverify.engines.run_sharded` takes `reproducible=`, an `sv.equivalent(...)`
  as the sinks take it: `floats="plan"` splits `SUM` and `AVG` of doubles
  within the proved bound, and `floats=sv.within(...)` splits them and raises
  where a row's bound exceeds the tolerance. `float_order=` warns
  (`"any"` is `floats="plan"`); `tolerance=True` still returns the bounds.

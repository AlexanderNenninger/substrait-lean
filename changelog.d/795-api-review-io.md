### Breaking: sources, sinks and the top level of 1.x

From the API review before 1.0 (`api-review/PROPOSAL.md`, items 11 and 12).
Each old form below still works in this release with a `DeprecationWarning`
that names the new one, except the snake_case values.

Sources and sinks (E2–E5):

- `contract(version=None)` reads the recorded contract on every source and
  sink: `DeltaSource`, `IcebergSource` (where `version` is a snapshot's
  sequence number, read from the metadata log), `DeltaSink`, `IcebergSink`
  and a `Sink` of your own. `Sink.committed()` is deprecated; a custom sink
  overrides `contract()`, and one that still overrides `committed()` works
  with a warning.
- `DeltaSource.contract(version)` reads the contract recorded up to
  `version`. Before, it returned the latest one, because delta-rs's history
  of a table loaded at an older version lists the latest commits
  ([DL-2](upstream/bugs/DL-2.json)).
- `DeltaSink.maintain(vacuum_retention=)` and
  `IcebergSink.maintain(snapshot_retention=, min_snapshots=)` take the
  constructors' names; `vacuum=` and `expire=` are deprecated. Every
  retention takes a `timedelta` or an ISO 8601 duration such as `"P7D"`.
- `StaticSource(table, name=..., version=...)` and
  `sverify.testing.source(rows, schema, name=...)` need `name=`, and
  `version` is keyword-only: two sources named `"table"` in one pipeline
  would collide.
- `SourceBatch.kind`, `SourceRefresh.mode` and `SinkWrite.mode` are
  snake_case: `"change_feed"`, `"snapshot_diff"`, `"row_level"`. Code that
  matches `"change feed"`, `"snapshot diff"` or `"row-level"` changes; the
  printed reports read as before.

The top level (A1–A4, A6):

- `Changes` is `sverify.io.Changes`, beside `StaticSource`, and
  `sv.from_substrait(data)` is `sv.Report.from_substrait(data)`, beside
  `Report.from_json`.

  ```python
  from sverify.io import Changes  # was: sv.Changes

  orders.apply(Changes(inserts=[(3, "cy", 50)]))
  report = sv.Report.from_substrait(exported)  # was: sv.from_substrait
  ```
- `sv.rows_per("customer", "day", at_most=3)` takes its columns as `unique`
  and `key` do; `rows_per(["customer", "day"], 3)` is deprecated.
- `sv.arrives_within("ts", "PT15M")` takes the lateness as a `timedelta` or
  an ISO 8601 duration; `days=`, `hours=`, `minutes=` and `seconds=` are
  deprecated.
- `sv.approx(cond, rel=, abs=, ulps=)` takes the tolerances of `sv.within`;
  the comparison moves by the largest of them, and by `rel=1e-6` when none
  is given.
- `sv.sql(query, name="orders")` names the chained table, the word every
  source uses; `as_=` is deprecated. `semantics` is typed as `Semantics`.
- A transform's report is `transform.report`, as a node's is
  `node.report`; `last_report` is deprecated, and `last_preconditions`
  (the refresh report says how each precondition was established).

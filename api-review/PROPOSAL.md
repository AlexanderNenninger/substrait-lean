# API review before 1.0

The 1.x stability promise ([#737](https://github.com/AlexanderNenninger/substrait-lean/issues/737),
[`docs/stability.md`](../docs/stability.md)) starts at 1.0: from then on the
formats only gain optional keys, and every Python break needs a release of
warnings and a migration note. This is the last round where a rename costs one
pull request. This proposal covers the whole public surface and asks for one
decision per item.

What it read:

- main at `05dc436a` (after [#788](https://github.com/AlexanderNenninger/substrait-lean/pull/788), report JSON);
- the open pull requests [#786](https://github.com/AlexanderNenninger/substrait-lean/pull/786) (the CLI, #744) and
  [#790](https://github.com/AlexanderNenninger/substrait-lean/pull/790) (quarantine, #184);
- M1's local branch `refactor/730-731` (module moves, not yet a pull request);
- the API reference's table of contents (`python/great-docs.yml`), which
  `docs/stability.md` makes the definition of "public";
- the schemas in `python/src/sverify/schemas/`;
- the issues on standards: [#775](https://github.com/AlexanderNenninger/substrait-lean/issues/775) (credentials),
  [#791](https://github.com/AlexanderNenninger/substrait-lean/issues/791) (ODCS),
  [#792](https://github.com/AlexanderNenninger/substrait-lean/issues/792) (OpenLineage),
  [#793](https://github.com/AlexanderNenninger/substrait-lean/issues/793) (SARIF, JUnit),
  [#794](https://github.com/AlexanderNenninger/substrait-lean/issues/794) (OpenTelemetry).

It changes no code. The surface was listed by introspection
(`inspect.signature` over every name in `__all__` of `sverify`,
`sverify.errors`, `sverify.io`, `sverify.engines` and `sverify.testing`), and
section N reruns six of the first critique's tasks
([`api-critique/`](../api-critique/REPORT.md), #686) against main.

Each item gives:

- Now: the current API.
- Proposed: the API this review proposes.
- Why: the reason for the change.
- Breaks: whether it breaks code, and whose.
- Effort: S is under half a day, M one to two days, L more.

"Breaks: new in #790" means the name has not been released, so changing it
costs nothing. Items marked "format" change a document that 1.x freezes.

Contents:

- A. Top level and contracts
- B. `Report`
- C. The `on_*` family and the knobs for "not proved"
- D. Nodes and refresh
- E. `sverify.io`
- F. `sverify.engines`
- G. `sverify.testing`
- H. Errors and warnings
- I. The CLI
- J. Environment variables, extras and config
- K. The formats
- L. Standards
- M. Removals at 1.0
- N. The newcomer test, again
- O. Do before 1.0, ranked
- P. Fine as is

---

## A. Top level and contracts

### A1. Twenty top-level names; three of them belong elsewhere

- Now: `sverify.__all__` has 20 names and `dir(sv)` matches it (critique
  5.3 is fixed). Among them are `Changes`, used only as the argument of
  `io.StaticSource.apply`, and `from_substrait`, which returns a `Report`,
  while its inverse is `Report.to_substrait` and the JSON pair is
  `Report.to_json`/`Report.from_json`.
- Proposed: move `Changes` to `sverify.io`, beside `StaticSource`. Make
  `Report.from_substrait(data)` a classmethod, beside `from_json`. The top
  level drops to 18 names.
- Why: a name sits where it is used, and each format has a `to_*`/`from_*`
  pair on one class.
- Breaks: `sv.Changes` and `sv.from_substrait`. Keep both as aliases with a
  `DeprecationWarning` for one release, or drop them at 1.0 (section M).
- Effort: S.

### A2. Condition constructors take their columns three ways

- Now: `unique(*cols)`, `key(*cols)`, `rows_per(cols: Sequence, at_most)`,
  `references(col, *, to=)`, `max_rows(n)`,
  `arrives_within(col, *, days=0, hours=0, minutes=0, seconds=0)`.
- Proposed: `rows_per(*cols, at_most=)`, to match `unique` and `key`.
  `arrives_within(col, within)`, where `within` is a `timedelta` or an
  ISO 8601 duration string (`"PT15M"`), as the sinks' retention parameters
  take a `timedelta` already (`DeltaSink(log_retention=)`).
- Why: one way to pass columns, and one type for durations across the API
  (L6).
- Breaks: callers of `rows_per(["a", "b"], 3)` and of
  `arrives_within(..., minutes=15)`. Both can be read for one release with a
  warning.
- Effort: S.

### A3. `approx` and `within` name tolerances differently

- Now: `approx(cond, rel=1e-06)` relaxes a condition by a relative tolerance
  only. `within(abs=None, rel=None, ulps=None)` states a tolerance on doubles
  for `equivalent`.
- Proposed: `approx(cond, *, abs=None, rel=None, ulps=None)`, with the same
  keywords and meaning as `within`, and `rel=1e-6` when none is given.
- Why: one way to say "a tolerance". A user who learns `within` can write
  `approx` without reading its docstring.
- Breaks: no; `rel` keeps its place and its default.
- Effort: S, if the checker's `approx` supports `abs` and `ulps`; M if
  Lean's side needs them.

### A4. `sql(as_=...)` and an untyped `semantics`

- Now: `sql(query, /, *, as_=None, dialect="duckdb", semantics: str = "reference", **tables)`.
- Proposed: `name=` for `as_=`, the word every source and sink uses
  (`DeltaSource(name=)`, `from_query(name=)`). Type `semantics` as
  `Semantics`, as `transform` and `verify` do.
- Why: a trailing underscore marks a clash with a keyword; `name` has none
  and is the established word here.
- Breaks: callers of `as_=` (rare: the default comes from the node).
- Effort: S.

### A5. The engine lists still name DataFusion and lack Spark

- Now: `Engine = Literal["duckdb", "polars", "datafusion"]`
  (`engine.py:48`), `Semantics` has no `"spark"`, the CLI's `--engine` help
  says "duckdb, polars, datafusion or spark", the `all` extra installs
  DataFusion, and the API reference's "Engines and SQL" section says
  "DuckDB, Polars, DataFusion or Spark". The roadmap
  ([#757](https://github.com/AlexanderNenninger/substrait-lean/issues/757))
  supports DuckDB, Polars and Spark in 1.0, and DataFusion after it.
- Proposed: `Engine = Literal["duckdb", "polars", "spark"]`. Keep the
  DataFusion code and its extra, label them "experimental: outside the 1.x
  promise" in the docstrings and the extra's comment, and drop DataFusion
  from `all`. Add `"spark"` to `Semantics` when M3's profile
  ([#739](https://github.com/AlexanderNenninger/substrait-lean/issues/739)) lands.
- Why: the type, the docs and the CLI promise what 1.0 supports. A name in
  the reference is a 1.x promise (`docs/stability.md`).
- Breaks: no code; the type hint narrows.
- Effort: S.

### A6. `ContractedTransform` exposes its constructor and deprecated fields

- Now: `ContractedTransform(fn, requires, ensures, on_unproved, check_requires, engine, infer=True, semantics=..., on_inferred=...)`
  is exported (for type hints and `.check`) with a constructor that still
  takes `engine` and `infer`. Its results are `last_report` and
  `last_preconditions`, where `Node` has `report`.
- Proposed: users get a `ContractedTransform` from `@sv.transform` only:
  document it without a constructor, and make the constructor's arguments
  keyword-only. Drop `engine` and `infer` from it at 1.0 (M1). Rename
  `last_report` to `report`, as on `Node`, and make `last_preconditions`
  private (the refresh report carries them).
- Why: one way to build a transform, and one name for "the report of this
  thing".
- Breaks: readers of `last_report` (the VS Code extension and sverify-dbt in
  this repository; alias for a release).
- Effort: S.

## B. `Report`

`Report` has 47 public attributes and a 40-field constructor. Tools read
it through `to_json` now ([#736](https://github.com/AlexanderNenninger/substrait-lean/issues/736)),
so the Python attributes can shrink to what a person reads.

### B1. Seven views of the preconditions a proof needs

- Now:
  - `needed`: labels per table, as strings;
  - `needed_conditions`: Ibis deferreds or SQL per table, ready for `requires=`;
  - `needed_text`: the same in words;
  - `needs`: a list of `Needed` records;
  - `suggestions`: preconditions per unproved postcondition, as code;
  - `Issue.suggested`: labels per table, for one issue;
  - `needs_text()` and `needs_lines()`: deprecated methods for `needed_text`.

  The CLI reads `needs` (`_needs` in `cli/_main.py`), the VS Code extension
  reads `Issue.suggested`, and the report JSON writes `needs`,
  `issue.needs`, `issue.suggested`, `checked.suggested` and
  `route.suggested`.
- Proposed: `needs: list[Needed]` is the record. Give `Needed` a
  `condition` (the deferred or SQL string) and a `text`. One helper,
  `report.suggested_requires`, returns the whole `requires=` mapping, with
  the stated and needed conditions merged and ready to paste.
  `suggestions` becomes `{postcondition label: list[Needed]}`.
  `Issue.suggested` becomes `Issue.needs: list[Needed]`. Drop `needed`,
  `needed_text`, `needed_conditions`, `needs_text()` and `needs_lines()`.
- Why: the first critique asked for conditions back from a refusal (its
  section 4); sverify answered with three more attributes. One record type,
  read by the CLI, the extension, sverify-dbt and the JSON, removes four
  names and one shape.
- Breaks: readers of the dropped attributes (in-repo tools; the guide's
  "Inferred preconditions" section). Format: `issue.suggested`,
  `checked.suggested` and `route.suggested` become lists of `needed`
  objects in the report JSON (K5).
- Effort: M.

### B2. `Report.warnings` is always empty

- Now: "The `issues` that do not count against a proof. None do."
- Proposed: remove it. `errors` stays, and `issues` holds every issue.
- Why: an attribute that is always empty invites code that never runs.
- Breaks: readers of `warnings` (none found in the repository).
- Effort: S.

### B3. `observation` and `equivalence`: one concept, two names

- Now: the field `Report.observation` and the property
  `Report.equivalence` return the same thing. The class is `Observation`,
  built by `sv.equivalent(...)`. `reproducible=` takes an `Observation`.
  The report JSON's key is `observation`, the manifest's `observation` and
  `observation_components`, and `str(report)` prints "observes:".
- Proposed: "equivalence" everywhere. `Report.equivalence`, class
  `Equivalence`, the JSON key `equivalence` in the report, the route and the
  manifest (`equivalence_components`), and "equivalent up to:" in
  `str(report)`. Drop `Report.observation`.
- Why: the first critique (3.1) found that "observation" reads as "a data
  point". The function users write is `sv.equivalent`, so the noun follows
  it.
- Breaks: readers of `report.observation` and the three JSON keys (format).
  Readers of 0.x documents map the old key.
- Effort: M (the manifest is in the proto's Struct and the fixtures).

### B4. Internal fields in the public constructor

- Now: `Report`'s public fields include `unchecked`, `optimized`,
  `rewrites`, `depends`, `contract`, `transfer`, `epsilon`, `rows_exact`,
  `floats_on`, `inferred_from`, `postconditions`, `conditions`, `stated`,
  `dialect`, `implied`, `bounds`, `relations`, `tie_places`,
  `windows_total` and `plan`. `str(report)` prints one of them raw:
  `epsilon: {'mean_t': {'abs': 1.998402245904532e-07, 'proved': {'abs': True}}}`
  (task 5, section N).
- Proposed: the public attributes are `verdict`, `proved`, `semantics`,
  `equivalence`, `requires`, `ensures`, `unproved`, `needs`, `issues`,
  `errors`, `assumed`, `facts`, `not_null`, `rows`, `deterministic`,
  `ties`, `routes`, `inputs` and `notes`, and the methods `route`, `run`,
  `to_json`, `from_json`, `to_substrait`, `from_substrait` (A1) and
  `substrait_contract`. The rest get an underscore. `plan` becomes
  `internal_plan`, as on `Node`. The constructor is documented as internal.
- Why: every public field is frozen for 1.x. The JSON (K5) carries what
  tools need.
- Breaks: readers of the hidden fields (the CLI, the VS Code extension and
  sverify-dbt read some; each needs a check).
- Effort: M.

### B5. `deterministic=` and `reproducible=` on `run`

- Now: `Report.run(deterministic: bool = False, reproducible: Observation | None = None)`.
  The docstring says `deterministic=True` is `reproducible=sv.equivalent()`.
  `engines.to_sql` and `engines.run_spark` take `deterministic=` (and the
  deprecated `tie_free=`). `Node.refresh` and the sinks take only
  `reproducible=`.
- Proposed: `reproducible=` everywhere, `deterministic=` nowhere as a
  parameter. `Report.deterministic` stays as a fact.
- Why: two knobs for one setting, and they interact (what does
  `deterministic=True, reproducible=sv.equivalent(rows="multiset")` mean?).
- Breaks: callers of `deterministic=` (warn for a release).
- Effort: S.

### B6. `streaming=` only on `Report.run`

- Now: `Report.run(streaming="allow" | "require")` refuses a Polars plan
  that falls back to the in-memory engine. `Node.refresh` has no such
  parameter, though refresh is how pipelines run, and the roadmap targets
  Polars streaming.
- Proposed: `refresh(streaming=)` and `Group.refresh(streaming=)`, with the
  same values.
- Why: the same choice on both ways to run a plan.
- Breaks: no.
- Effort: S.

## C. The `on_*` family and the knobs for "not proved"

### C1. Three `on_*` parameters, three vocabularies

- Now:
  - `on_unproved`: `"error" | "runtime" | "warn"`;
  - `on_inferred`: `"error" | "warn" | "silent" | "off"`;
  - `on_violation` (#790): `"raise" | "quarantine" | "skip_batch"`, with
    the refresh outcomes `"ok" | "quarantined" | "held"`.
- Proposed: one vocabulary, where each value names what happens.
  - `"error"` raises, in all three: `on_violation="error"` replaces `"raise"`.
  - `"warn"` goes on and warns with a `SverifyWarning` subclass (H2).
  - `"ignore"` goes on silently: `on_inferred="ignore"` replaces `"silent"`.
    It is the word of Python's warning filters.
  - `"check"` checks on the data at run time: `on_unproved="check"`
    replaces `"runtime"`. It is the word the reports print ("checked on
    data") and the one `check_requires=` uses.
  - `"off"` turns inference off (`on_inferred` only).
  - `"quarantine"` and `"hold"` (for `"skip_batch"`) in `on_violation`. Each
    policy's verb matches its outcome: quarantine gives "quarantined", hold
    gives "held".
- Why: a user who learns one `on_*` knows the others. `"raise"` beside
  `"error"` and `"skip_batch"` beside `"held"` are two words for one thing.
- Breaks: `on_unproved="runtime"` and `on_inferred="silent"` (warn for a
  release). `on_violation`'s values are new in #790.
- Effort: S, done inside #790 for `on_violation`.

### C2. `check_requires=False` and `on_violation` interact

- Now: `transform(check_requires=False)` skips the checks on data that
  `on_violation` acts on.
- Proposed: `check_requires=False` with an `on_violation` other than
  `"error"` raises `ValueError` at the decorator.
- Why: a knob that silently disables another.
- Breaks: no; the combination does nothing today.
- Effort: S.

### C3. `on_unproved="warn"` and `unverified=True` (fixed)

`on_unproved="warn"` now runs the node with `UnverifiedRunWarning` at each
refresh (task 6b in section N), as critique 2.7 asked. `unverified=True`
stays for a one-off run. No change.

## D. Nodes and refresh

### D1. "view" survives in text and in the sink record

- Now: refresh text prints `view double_charges4: payments@v1`. The sink
  contract record's key is `view`, and so is `Contract.view` and the sinks'
  `view` attribute. Users meet "node", "transform" and "stage";
  `IncrementalView` left the public API in 0.2.0.
- Proposed: `node` in the record (format, K3), `Contract.node`, and
  "node double_charges4: payments@v1" in the text. The sinks' `view`
  attribute becomes private (E1).
- Why: one name for the thing a user built.
- Breaks: format (the reader maps `view` from older records); readers of
  `Contract.view`.
- Effort: S.

### D2. Quarantine's names (#790)

- Now: `Node.write(sink, *, quarantine: Sink | bool | None = None)`,
  `Node.quarantined(source=None)`, and on `StageRefresh`: `quarantine`,
  `quarantine_table`, `set_aside`, `held` and `held_error`.
  `Refresh.outcome`, `Refresh.alert()` and `Refresh.to_json()`.
- Proposed: keep the shape; make `quarantine=` take `Sink | None` and
  `False` (an explicit "no quarantine table"), with `True` dropped, since it
  means what `None` means. Use C1's values. Name the rows count
  `quarantined` (the participle the outcome uses) for `set_aside`.
- Why: the policy, the outcome and the count share one word.
- Breaks: new in #790.
- Effort: S.

### D3. `Refresh.to_json` and the quarantine table are two more formats

#790 adds `refresh.schema.json` and `quarantine.schema.json` to
`docs/stability.md`. They are covered by K, and their fixtures go into
`tests/formats/`. No separate change.

## E. `sverify.io`

### E1. Internals in the documented classes

- Now: the documented sinks expose `view`, `keeps_retired`,
  `create_options_ignored` and `reproducible`; the sources `hi_slack`;
  `SinkChange.native`. `FlightLog`, a Flight server for examples and tests
  with fifteen server methods, is in `sverify.io.__all__`.
- Proposed: underscore the internal attributes (keep `reproducible`, which
  is a constructor argument). Move `FlightLog` to `sverify.testing`.
- Why: a public attribute is frozen for 1.x.
- Breaks: readers of these attributes (none outside the package found);
  `sverify.io.FlightLog` (alias for a release).
- Effort: S.

### E2. Reading a stored contract: three names

- Now: `DeltaSource.contract(version=None)`, `IcebergSource.contract()`
  (no version), `DeltaSink.committed()` and `IcebergSink.committed()`, and
  `stored()` on both sources. `DeltaSource.table(version=None)` and
  `IcebergSource.table()` differ the same way.
- Proposed: `contract(version=None)` on every source and sink, with
  Iceberg's `version` a snapshot id. `table(version=None)` on both sources.
  Keep `stored()` if it returns something other than the contract, and say
  what in one line.
- Why: Delta and Iceberg are both first class in 1.0 (#757). One method
  name per question.
- Breaks: callers of `committed()` (alias for a release).
- Effort: S.

### E3. Maintenance parameters

- Now: `DeltaSink(checkpoint_interval=, log_retention=, vacuum_retention=, compact_every=)`
  with `maintain(vacuum=)`; `IcebergSink(snapshot_retention=, min_snapshots=, compact_every=)`
  with `maintain(expire=, min_snapshots=)`.
- Proposed: keep each format's own terms (Delta's `logRetentionDuration`
  and `deletedFileRetentionDuration`, Iceberg's snapshot expiry). Make each
  `maintain` take the constructor's names: `maintain(vacuum_retention=)` and
  `maintain(snapshot_retention=, min_snapshots=)`. Durations take a
  `timedelta` or an ISO 8601 string (L6).
- Why: one name per setting within a class.
- Breaks: callers of `maintain(vacuum=)` and `maintain(expire=)`.
- Effort: S.

### E4. Source names and defaults

- Now: `StaticSource(table, version=0, *, name="table")` and
  `testing.source(rows, schema=None, *, name="table", version=0)` default
  the name to `"table"`. `from_files`, `from_frame` and `from_query` require
  `name=`. `DeltaSource` derives it from the path. `version` is positional
  in one and keyword-only in the other.
- Proposed: `name` is required and keyword-only wherever it cannot be
  derived, `StaticSource` included. `version` is keyword-only in both.
- Why: two static sources named `"table"` in one pipeline collide, and
  the default hides it until a refresh.
- Breaks: `StaticSource(t)` without a name, and `StaticSource(t, 3)`.
- Effort: S.

### E5. Enumerated values with spaces and hyphens

- Now: `SourceBatch.kind` is `"change feed" | "snapshot diff"`,
  `Batch.kind` is `"append" | "snapshot" | "changes"`, and
  `SinkWrite.mode` includes `"row-level"`. The CLI's JSON uses
  `"not_proved"` and `"budget_exceeded"`, and its codes `"may-be-false"`.
- Proposed: snake_case for every fixed-set value in Python and in JSON:
  `"change_feed"`, `"snapshot_diff"`, `"row_level"`. Kebab case stays for
  CLI flags only.
- Why: values a program matches on should be identifiers. They are frozen
  where they reach a format (K4).
- Breaks: code that matches on `"change feed"`, `"snapshot diff"` or
  `"row-level"`.
- Effort: S.

### E6. Credentials (#775)

- Now: `storage_options=` (delta-rs's term), `Storage(options | callable)`,
  pyiceberg's `catalog`, and `FlightSource(token=str)`. #775 proposes
  `credentials="<name>"` and `secret="env:NAME"`.
- Proposed: keep `storage_options` and `catalog`, the libraries' own
  terms. When #775 lands, add one parameter, `credentials=`, taking a
  reference (`"env:NAME"`, `"aws-sm:..."`, …), and no second one. Change
  `FlightSource(token=)` to accept such a reference too.
- Why: one name for "where the secret comes from" across sources, sinks
  and catalogs.
- Breaks: no (additive).
- Effort: part of #775.

## F. `sverify.engines`

### F1. `Dialect` documents 140 SQL-writing methods

- Now: `engines.Dialect` is in the API reference, so its methods
  (`int_add`, `decimal_window_sum`, `float_rank`, …) are public by the
  stability policy's definition.
- Proposed: document `Dialect` with its four fields (`name`, `guards`,
  `finite`, `decimals`) and the constants `DUCKDB`, `SNOWFLAKE` and
  `SPARK`. State that subclassing it is outside the 1.x promise, and mark
  the writer methods private in the docs (the API reference's member
  filter).
- Why: the SQL writer changes whenever a function lands. Freezing 140
  method signatures for 1.x would block that work.
- Breaks: no code.
- Effort: S.

### F2. Two ways to run on Spark

- Now: `engines.run(con, plan, engine="spark" | <SparkSession>)` and
  `engines.run_spark(plan, tables, spark=None, *, deterministic=, tie_free=)`.
- Proposed: one entry point, `run(..., engine=<SparkSession> | "spark")`.
  Drop `run_spark` at 1.0 or keep it as an undocumented helper.
- Why: more than one way to do one thing.
- Breaks: callers of `run_spark` (examples and the Spark notebook).
- Effort: M (M3 is reworking Spark anyway; do it there).

### F3. Module functions beside `Connection`'s methods

- Now: `engines.create_table(con, name, schema, rows)` and
  `engines.table_rows(con, name)` beside `con.put`, `con.get`,
  `con.table`, `con.schema`, `con.has` and `con.drop`. `sv.connect(engine)`
  and `engines.Connection(engine)` both build a connection.
- Proposed: `con.create(name, schema, rows=())` and `con.rows(name)`, and
  drop the two module functions. `Connection`'s attributes `arrow` and
  `ibis` (the tables and the Ibis backend it reads through) become private
  behind `con.get` and `con.table`. Document `sv.connect` as the way to get a
  `Connection`, and the class for type hints.
- Why: one way per operation, found by tab completion on `con`.
- Breaks: callers of `create_table` and `table_rows` (alias for a release).
- Effort: S.

### F4. The plan layer

- Now: `substrait_json(con, sql, semantics="duckdb")` defaults to
  `"duckdb"`, where `verify`, `sql` and `transform` default to
  `"reference"`. `run(con, plan_json)`, `run_substrait_json`,
  `written_plan`, `delta_plans` and `to_sql(plan, dialect, *, unchecked=...)`
  take sverify's internal plan as a JSON string, and `unchecked` is an
  internal dict. `to_sql` is reached through `json.loads(node.plan)`
  (critique 7.4).
- Proposed: `Report.to_sql(dialect)` and `Node.to_sql(dialect)`, beside
  `to_substrait`, as the documented way to get SQL. Move `substrait_json`,
  `run_substrait_json`, `written_plan` and `delta_plans` to the "Plans"
  section with a note that they are low level and may change in a minor
  release, or keep them out of the 1.x promise by name. Default
  `substrait_json`'s `semantics` to `"reference"`, or make it required.
- Why: the promise covers what users need. A default that differs from
  every other one is a trap.
- Breaks: `substrait_json` callers that relied on the default.
- Effort: M.

### F5. `engines.Unsupported`

- Now: `engines.Unsupported` and `errors.Unsupported` are both exported and
  both documented.
- Proposed: `sverify.errors` only (H1 renames it).
- Breaks: imports from `sverify.engines` (alias for a release).
- Effort: S.

### F6. `run_sharded`'s float vocabulary

- Now: `run_sharded(..., float_order="exact", tolerance: bool = False)`.
- Proposed: `run_sharded(..., reproducible=None)` with an `Equivalence`
  (B3), the type every other entry point takes for "what must match".
- Why: one way to state a tolerance.
- Breaks: callers of `float_order` and `tolerance` (few; the parameter is
  from the sharding work).
- Effort: M.

## G. `sverify.testing`

### G1. Two shapes for test data

- Now: `assert_contract(node, data=None, *, expected=None, engine="duckdb")`
  takes `{"orders": [tuples]}`; `cases(node, *, max_rows=5)` yields
  `{"orders": pyarrow.Table}`; `assert_engines_agree(node, data, *, engines=None)`.
- Proposed: `data=` and `expected=` accept a `pyarrow.Table`, a list of
  tuples or a list of dicts, in all three (critique 7.2).
- Why: one shape a test can pass along from `cases` to `assert_contract`.
- Breaks: no.
- Effort: S.

### G2. `engine=` and `engines=`

`assert_contract(engine=)` and `assert_engines_agree(engines=)` are
singular and plural for one and several. Fine as is.

## H. Errors and warnings

### H1. Exception names without `Error`

- Now: `NotIncremental` and `Unsupported` subclass `SverifyError` without
  the suffix PEP 8 asks of exceptions that are errors.
- Proposed: `NotIncrementalError` and `UnsupportedError`. The CLI's status
  for it is `"unsupported"` (I1), and "refused" stays the word for a route
  that refuses (`RouteError`, class `refused`).
- Why: PEP 8, and one word per concept.
- Breaks: `except Unsupported` and `except NotIncremental` (aliases for a
  release).
- Effort: S.

### H2. Warnings have no common base, and two are plain `UserWarning`

- Now: `UnverifiedRunWarning`, `EngineSettingsWarning` and
  `EngineVersionWarning` subclass `UserWarning`. `on_unproved="warn"` and
  `on_inferred="warn"` warn with a plain `UserWarning` whose text ends
  "(e.report has the details)", where no `e` exists (task 6b).
- Proposed: `SverifyWarning(UserWarning)` in `sverify.errors`, the base of
  every warning sverify issues. `UnprovedWarning` and `InferredWarning` for
  the two `on_*="warn"` cases, each with `.report`. The message says
  "(`.report` has the details)".
- Why: `filterwarnings("error", category=SverifyWarning)` in a CI job
  turns every sverify warning into a failure, and nothing else.
- Breaks: no (subclasses of `UserWarning`).
- Effort: S.

### H3. The reference documents 11 of 20 errors

- Now: the API reference's "Errors" section lists 11; `RouteError`,
  `UnverifiedRunError`, `CheckerVersionError`, `ConcurrentWriteError`,
  `EngineSettingsError`, `EngineVersionError` and the three warnings are
  missing.
- Proposed: document all, grouped: proof (`VerificationError`,
  `CompositionError`, `UnverifiedRunError`), data (`PreconditionError`,
  `PostconditionError`, `SchemaError`, `AuditError`), running
  (`RouteError`, `NotIncrementalError`, `ConcurrentWriteError`,
  `UnsupportedError`, `SqlError`, `ExportError`), setup (`CheckerVersionError`,
  `EngineVersionError`, `EngineSettingsError`), and the warnings.
- Breaks: no.
- Effort: S.

### H4. A code on every error

- Now: the CLI derives a code from the exception's type (`_exception` in
  `cli/_main.py`), and from a report's `reason` or issue `kind`.
- Proposed: `SverifyError.code`, a snake_case string from the same set as
  the report's reasons (K6), set by each subclass.
- Why: the CLI, SARIF (#793), OpenTelemetry (#794) and OpenLineage (#792)
  each need a stable code per failure; one attribute serves all four.
- Breaks: no.
- Effort: S.

## I. The CLI (#786)

### I1. Exit code 2 means two things

- Now: 0 proved, 1 not proved, 2 refused (`Unsupported`), 3 budget
  exceeded, 4 error. argparse exits with 2 on a usage error, so a typo in a
  flag reads as "refused". #790's notes propose 3 for "quarantined or
  held", which is the budget's code.
- Proposed:

  | Code | Meaning |
  |---|---|
  | 0 | proved; a refresh committed every row |
  | 1 | not proved |
  | 2 | usage error (argparse, a bad target) |
  | 3 | unsupported or refused |
  | 4 | time or memory budget exceeded |
  | 5 | refresh committed with rows quarantined, or held a node |
  | 6 | error: the file raised, I/O, a crash |

  `sverify --help` and the docs list the table. The JSON's `status` values
  are `proved`, `not_proved`, `usage`, `unsupported`, `budget_exceeded`,
  `quarantined`, `held` and `error`.
- Why: 2 for usage errors is the convention of POSIX utilities, argparse,
  mypy and ruff. Codes 3 and 5 keep "the pipeline needs attention" apart
  from "the tool failed".
- Breaks: new in #786.
- Effort: S.

### I2. `explain` does two jobs

- Now: `sverify explain may-be-false` explains a code; `sverify explain
  file.py:node` prints a node's full report.
- Proposed: `explain <code>` explains, and `check --full file.py:node` (or
  `sverify report file.py:node`) prints the report.
- Why: one meaning per command; a code that looks like a path (or a file
  named after a code) is ambiguous.
- Breaks: new in #786.
- Effort: S.

### I3. `suggest --apply` beside `check`

- Now: `sverify suggest file.py --apply` writes needed preconditions into
  `requires=`, then checks again.
- Proposed: `sverify check --fix` and `check --diff`, as ruff names the
  same step. Drop `suggest`.
- Why: a linter's users know `check --fix`; one command fewer.
- Breaks: new in #786.
- Effort: S.

### I4. `--json` and the formats to come

- Now: `--json`. #793 plans `--format sarif|junit`.
- Proposed: `--format text|json|sarif|junit` (`--output-format`, ruff's
  name, as an alias), with `--json` as the short form of `--format json`.
- Why: one flag for "how to print", which takes new values without new
  flags.
- Breaks: new in #786.
- Effort: S.

### I5. The CLI's JSON is a fifth document, marked provisional

- Now: each item carries `name`, `status`, `verdict`, `summary`,
  `problems`, `needs` and `facts`, and the document says
  `"format": "provisional"`. #788 has landed, so `Report.to_json()` exists.
- Proposed: `{"format": 1, "sverify", "command", "exit", "status",
  "items": [{"name", "nodes", "status", "summary", "report": <Report.to_json()>}]}`
  with a schema in `schemas/check.schema.json`. `verdict`, `needs` and
  `facts` come from the embedded report. `problems` becomes a view the
  human output prints, or the SARIF results (I4).
- Why: one source for each fact, and a format 1.x freezes on purpose.
- Breaks: new in #786.
- Effort: M.

### I6. `--timeout` takes seconds; Python has no timeout

- Now: `--timeout` and `SVERIFY_TIMEOUT` take seconds (default 30, 0 turns
  it off). `verify` and `transform` take no budget (#745).
- Proposed: the CLI and the environment accept a number of seconds or an
  ISO 8601 duration (`PT2M`). When #745 adds a budget to Python, it is
  `timeout=` (a `timedelta` or seconds), the CLI's word.
- Why: one name for one setting in every layer (L6).
- Breaks: no.
- Effort: S.

### I7. `--engine` and the run flags

- Now: `refresh --engine` lists DataFusion; `refresh` has `--audit` and no
  `--unverified` or `--streaming`.
- Proposed: the engines of A5. Add `--unverified` and
  `--streaming=allow|require` when someone asks; the names are the Python
  keywords in kebab case.
- Breaks: no.
- Effort: S.

### I8. Colour

The CLI prints no colour today. When it does, it honours `NO_COLOR` and
`FORCE_COLOR`, and takes `--color=auto|always|never`. Nothing to change now.

## J. Environment variables, extras and config

### J1. `SVERIFY_CHECK` names the binary, and reads as the command

- Now: `SVERIFY_CHECK` is the path to the `substrait-check` binary;
  `SVERIFY_PREBUILT_CHECK` is a build-time switch. With a `sverify check`
  command, `SVERIFY_CHECK=…` reads as a setting of that command.
- Proposed: `SVERIFY_CHECKER` and `SVERIFY_PREBUILT_CHECKER`, reading the
  old names for a release with a warning.
- Breaks: contributors and CI that set the old names.
- Effort: S.

### J2. Variables in one table, and a config file

- Now: `SVERIFY_CHECK`, `SVERIFY_COUNTEREXAMPLES`, and with #786
  `SVERIFY_TIMEOUT`, `SVERIFY_MEMORY_LIMIT` and `SVERIFY_SPILL_DIRECTORY`.
  They are documented in docstrings. There is no config file.
- Proposed: one table in the guide, each variable with its flag and its
  Python keyword. `SVERIFY_TEMP_DIRECTORY` for `SVERIFY_SPILL_DIRECTORY`,
  since it sets DuckDB's `temp_directory`. Reserve `[tool.sverify]` in
  `pyproject.toml` (the place ruff, mypy and pytest read) for later, with
  its keys the flags' names in snake case. The order is flag, environment,
  `[tool.sverify]`, default.
- Why: a CI author looks in one place; names map one to one.
- Breaks: `SVERIFY_SPILL_DIRECTORY` is new in #786.
- Effort: S now (the table and the rename); the config file after 1.0.

### J3. Extras

- Now: `datafusion`, `polars`, `spark`, `delta`, `iceberg`, `flight`,
  `testing` and `all`; `all` includes DataFusion. `iceberg` cannot open a
  local catalog without `pyiceberg[sql-sqlite]` (critique 7.5).
- Proposed: drop DataFusion from `all` (A5). `iceberg` installs
  `pyiceberg[pyarrow,sql-sqlite]`. Keep the other names; they are the
  packages' names, normalized as PEP 685 asks.
- Breaks: users of `sverify[all]` who use DataFusion.
- Effort: S.

## K. The formats

1.x freezes these on release. Every item here is breaking now and impossible
later.

### K1. `profile` beside `semantics`

- Now: the report JSON says `semantics`; each route in it says `profile`,
  and so does the Substrait manifest. Python says `semantics` (`Route.profile`
  is the one exception).
- Proposed: `semantics` in the route, the manifest and `Route`.
- Why: critique 3.1 found two names for one concept; the code kept both.
- Breaks: format; readers map `profile`.
- Effort: S.

### K2. `observation` (B3)

`equivalence` in the report, the route and the manifest.

### K3. The sink record's keys

- Now: Delta keeps the record under the commit's `commitInfo` key
  `sverify`; Iceberg under the table property `sverify.contract`, and #790
  adds `sverify.quarantine` on both. The record's `view` names the node.
- Proposed: `sverify.contract` on Delta as on Iceberg, read back from
  `sverify` for tables written before 1.0. `node` for `view` (D1).
- Why: one key per record on both formats, and namespaced keys that leave
  room for the next record.
- Breaks: format, for 0.x tables (the reader handles both).
- Effort: S.

### K4. Fixed sets in snake_case

E5's values, where they reach a format (`SinkWrite.mode` in the refresh
JSON, `kind` of a source batch). The manifest's `class` values
(`exact`, `observed`, `shim`, `refused`) and `evidence` are fine.

### K5. Duplicates inside the report JSON

- Now:
  - `hints` at the top and `hint` in each issue;
  - `ties` (labels) and `tie_places` (relation, op, what);
  - `suggested` in issues, conditions and routes, beside `needs` (B1);
  - `issue.expr` and `issue.shown`, beside `issue.message`;
  - `verdict` beside `proved`;
  - the manifest's `rows` is a `number`, the report's an `integer`.
- Proposed: drop the top-level `hints`. One `ties` list of
  `{relation, op, what, keys}`. `needs` lists of `needed` objects for every
  `suggested` (B1). Keep `issue.shown` (the user's form) and drop
  `issue.expr` unless a tool needs the internal one. Keep `verdict` as the
  display line and say so in the schema. `rows` an integer in both.
- Why: a frozen format with two keys for one fact keeps both forever.
- Breaks: format; no reader outside the repository yet.
- Effort: M.

### K6. One set of codes, with a level

- Now: a condition's `reason` and an issue's `kind` are snake_case
  (`may_be_false`). The CLI turns them into kebab case (`may-be-false`) for
  `explain`. An issue has `error: bool`.
- Proposed: one spelling, snake_case, in the JSON, the CLI's output,
  `explain` (which also accepts kebab case) and `SverifyError.code` (H4).
  Each finding gets `level: "error" | "warning" | "note"`, SARIF's levels,
  for `error: bool`. The codes and their explanations live in one table in
  the package (today `cli/_explain.py`), which the docs render.
- Why: SARIF's `ruleId` and `level` (#793) become a copy, and a code
  means the same in every output.
- Breaks: format (`error` becomes `level`); the CLI's codes are new.
- Effort: S.

### K7. Schema identifiers

- Now: each schema's `$id` is a GitHub path on main
  (`https://github.com/.../python/src/sverify/schemas/report.schema.json`).
- Proposed: a versioned `$id`, `https://alexandernenninger.github.io/substrait-lean/schemas/report/1.json`
  (the docs site, which publishes the files), and the same in each document
  as `$schema`. OpenLineage facets need this `_schemaURL` form too (L3).
- Why: a `$id` names one version of a schema, and a path on main moves.
- Breaks: no reader dereferences it yet.
- Effort: S.

### K8. A source location for SARIF

- Now: the report JSON has no file or line.
- Proposed: `location: {file, line}` of the transform (and, where #691's
  spans give one, of each finding's expression).
- Why: SARIF results without a location do not show on pull request lines
  (#793).
- Breaks: no (an optional key).
- Effort: S, and it can land after 1.0 as an optional key.

## L. Standards

Where a standard exists, sverify's term is checked against it here.

### L1. SARIF 2.1.0 (#793)

A result is `ruleId`, `level`, `message.text`, `locations` and optional
`fixes`. K6 gives `ruleId` and `level`, K8 the location, and B1's
`Needed.condition` the fix. Sverify's word for a finding varies:
"problem" (CLI JSON), "issue" (report), "reason" (condition). Proposed:
"finding" in docs and the CLI's output, kept as `issues` and `reason` in
the frozen JSON. Not breaking.

### L2. OpenTelemetry (#794)

No telemetry exists yet; decide the names before the first release that
has it, so dashboards built on it keep working.

- Configuration through the standard `OTEL_*` variables only, and no
  `SVERIFY_OTEL_*`.
- Span names `sverify.check`, `sverify.refresh`, and the children
  `sverify.lift`, `sverify.prove`, `sverify.counterexamples`, `sverify.plan`,
  `sverify.run`, `sverify.commit`.
- Attributes in the `sverify.` namespace, snake_case segments, following
  the semantic conventions' naming rules: `sverify.node`, `sverify.engine`,
  `sverify.route.kind`, `sverify.route.class`, `sverify.semantics`. The
  engine also goes in `db.system.name` where the conventions list it
  (`duckdb` is not in the registry today; check the version pinned).
- Metrics with UCUM units: `sverify.proof.duration` (histogram, `s`),
  `sverify.memory.peak` (`By`), `sverify.rows.read`, `sverify.rows.written`,
  `sverify.rows.quarantined` (`{row}`).
- Error type on spans as `error.type`, set to H4's code.

Not breaking (new). Effort: S to write down in #794.

### L3. OpenLineage (#792)

A custom facet's name carries a producer prefix and the facet a
`_producer` and `_schemaURL`. #792's `sverify_contract` follows that.
Proposed: `_schemaURL` uses K7's versioned URL; the job is the node
(`namespace` the pipeline file or project, `name` the node's name, D1),
and the facet's keys reuse the report JSON's names (`semantics`,
`equivalence`, `routes`, `class`), so no third vocabulary appears. Not
breaking.

### L4. ODCS (#791)

ODCS v3 says `schema`, `properties`, `required` (not null), `unique`,
`primaryKey`, and `quality` rules. Sverify's `requires`/`ensures` follow
design by contract (Eiffel's terms), which is the older standard and fits
the proofs. `sv.key` is ODCS's `primaryKey` (unique and required), and the
sink record's `not_null` its `required`. Proposed: keep sverify's names and
map them in the export, with the table of correspondences in the docs.
Check the ODCS version before building, as #791 says. Fine as is.

### L5. OIDC and credentials (#775)

GitHub's OIDC token comes from `ACTIONS_ID_TOKEN_REQUEST_URL` and
`ACTIONS_ID_TOKEN_REQUEST_TOKEN`; the cloud SDKs read `AWS_*`,
`GOOGLE_APPLICATION_CREDENTIALS` and `AZURE_*`. Proposed: sverify reads
none of these itself and passes each library's own chain through (delta-rs,
pyiceberg, the cloud SDKs). E6's `credentials=` names a secret, never a
value, and adds no `SVERIFY_*` credential variable. Not breaking.

### L6. ISO 8601 durations and times

- Now: durations are `timedelta` in sink parameters, keyword numbers in
  `arrives_within`, float seconds in `FlightSource(timeout=)` and the CLI's
  `--timeout`.
- Proposed: every duration parameter takes a `timedelta`, and every one
  that comes from text (CLI, environment, a future `[tool.sverify]`, ODCS
  SLAs) also takes an ISO 8601 duration string. Timestamps in the formats
  are RFC 3339 with an offset. `FlightSource(timeout=)` takes a
  `timedelta` or seconds.
- Breaks: `arrives_within` (A2).
- Effort: S.

### L7. PEP 8 and Python conventions

Covered above: exception names (H1), `as_=` (A4), fixed-set values (E5),
keyword-only optional arguments (E4). `Route.cls` is the usual spelling
for a field that cannot be called `class`; fine. The library is synchronous
throughout; no `async` API exists, and none is needed for 1.0.

## M. Removals at 1.0

The deprecated aliases from #724, #690 and #695. 0.5.0 shipped on
2026-11-05 without them, so the next release (0.6) carries their warnings,
and 1.0 can drop them under the stability page's "one minor release" rule.

| Name | Replacement |
|---|---|
| `transform(engine=)` | `check_engine=` |
| `transform(infer=)`, `verify(infer=)`, `ContractedTransform.infer` | `on_inferred="off"` |
| `Report.run(check_inputs=)` | `check_requires=` |
| `Report.needs_text()`, `Report.needs_lines()` | B1 |
| `Node.plan` | `Node.internal_plan` |
| `route="reference"` | `route="translated"` |
| `to_sql(tie_free=)`, `run_spark(tie_free=)` | `reproducible=` (B5) |
| `engines.Connection.datafusion` (`engine.py:154`) | none |

Breaks: callers that ignored the warnings. Effort: S, one pull request at
the 1.0 release candidate.

M1's moves (`refactor/730-731`) add `sverify.conditions` and
`sverify.report` as modules without underscores. The public names stay at
the top level, so these should be `_conditions` and `_report`, or listed in
`docs/stability.md` as internal, before a user imports from them. Effort: S,
in that branch before its pull request.

## N. The newcomer test, again

Six of the first critique's tasks (`t1`, `t2`, `t5`, `t6`, `t6b`, `t7b` in
`api-critique/tasks/`) ran against main at `05dc436a`, with today's checker
build, under `-W default`.

Better since the critique:

- A report's first line is its verdict ("NOT proved: 1 of 2 postconditions
  not proved, 1 possible runtime error"), and the exception is a count and
  one line per finding, with "(e.report has the details)". Critique 1.3 and
  1.4 are done.
- The expressions are the user's: `ts + ibis.interval(minutes=5)`,
  `(price - cost) * 100 // price`, `ts - lag(ts)`. No `$n`, no internal
  rewrites (1.1).
- The key lost through a self-join says why: "`dup_txn` comes from
  payments.txn_id, whose key unique(txn_id) is lost on the way: a join, a
  union or an UNNEST can repeat a value" (1.2).
- The NULL hint for `sd_t` is right: "to allow that, state
  `((_.sd_t >= 0) | _.sd_t.isnull())`", with the counterexample (1.2).
- Tolerances: "observes: … the plan's bound on its doubles is 2.0e-07; NOT
  met: no engine meets the tolerance; or declare sv.max_rows(50_039)",
  which names the bound, the fix and the alternative (2.6).
- Route lines read `route on duckdb: exact; evidence tested` (1.5).
- `on_unproved="warn"` runs with `UnverifiedRunWarning` (2.7).
  `PreconditionError` carries `source`, `condition` and `rows` (section 4).
  The SUM assumption names `on_inferred="off"` (2.9).
- `sv.key`, `sv.__version__`, `dir(sv) == __all__`, every error in
  `sverify.errors`, `to_substrait` on nodes and transforms, and
  `report.route(engine)` for "where can this run" are there (section 4,
  5.3, 5.4).
- `strict=` is gone (`TypeError`); `infer=` and `needs_lines()` warn and
  name their replacement.

Still awkward:

- The preconditions a proof needs come in seven forms (B1). In task 6 the
  newcomer printed `needed`, `needs_lines()` and `suggestions` and got a
  dict of strings, a deprecation and an empty dict.
- `str(report)` prints `epsilon: {'mean_t': {'abs': 1.998402245904532e-07, 'proved': {'abs': True}}}`
  under "known about the output" (task 5): an internal field, sixteen
  digits (B4).
- The `on_unproved="warn"` build warning is a plain `UserWarning` whose
  text says "(e.report has the details)" (task 6b, H2).
- Refresh text says `view double_charges4: payments@v1` (D1).
- "observes:" and "the observation" in the text, `equivalence` on the
  report, `observation` in the JSON (B3).
- `//` and `%` on `-7` under the reference give `q = -4`, `r = -1`, so
  `q*2 + r == x` fails (task 7b), as in critique 2.4. This is Ibis's
  meaning, and the guide's section on integer division is still the fix.
  Not an API item.
- `session_no >= 1` (a running sum of 0/1) is still not provable (task 2).
  A precision item for the range analysis, after 1.0.

## O. Do before 1.0, ranked

Ranked by what 1.x would freeze and how many users meet it.

1. K1, K2/B3, K3, K5, K6: the format renames (`semantics`, `equivalence`,
   `sverify.contract`, `node`, one `ties`, codes with a level). Frozen at
   1.0, no outside readers yet.
2. C1 and D2: one vocabulary for `on_unproved`, `on_inferred` and
   `on_violation`, settled inside #790 before it merges.
3. I1, I2, I3, I4, I5: the CLI's exit codes, commands, `--format` and its
   JSON, settled inside #786 before it merges.
4. B1: one record for needed preconditions.
5. B4 and E1: hide internal fields of `Report`, the sinks and the sources,
   and move `FlightLog`.
6. F1 and F4: keep `Dialect`'s methods and the plan layer out of the 1.x
   promise; add `Report.to_sql` and `Node.to_sql`.
7. M: drop the deprecated aliases; make M1's new modules private.
8. A5 and J3: the engine lists and extras say what 1.0 supports.
9. H1, H2, H3, H4: exception names, `SverifyWarning`, the documented list,
   `.code`.
10. B5 and F6: `reproducible=` as the one knob.
11. E2, E3, E4, E5: `contract()` on every source and sink, `maintain`'s
    names, required `name=`, snake_case values.
12. A1, A2, A3, A4, A6: `Changes` and `from_substrait` moved, condition
    arguments, `approx`'s tolerances, `sql(name=)`, `ContractedTransform.report`.
13. F2, F3: one way to run on Spark (with M3), `Connection` methods.
14. J1, J2: `SVERIFY_CHECKER`, `SVERIFY_TEMP_DIRECTORY`, the variables'
    table.

Items 1 to 3 are the cheapest now and the dearest later. The work splits
by area, so sessions don't share files: formats (1), #790 (2), #786 (3), `Report` (4, 5, 10), engines
(6, 13), and a sweep (7, 8, 9, 11, 12, 14).

## P. Fine as is

- The top level otherwise: `transform`, `verify`, `unique`, `key`,
  `references`, `max_rows`, `rows_per`, `arrives_within`, `approx`,
  `equivalent`, `within`, `sql`, `connect`, `group`, `asof_join`, `Node`,
  `Report`, `ContractedTransform`.
- `requires`/`ensures`: design by contract's terms (L4).
- `Node`'s properties for data (`report`, `schema`, `table`, `versions`)
  and methods for work (`refresh`, `status()`, `to_arrow()`); `Group.refresh`
  with `Node.refresh`'s parameters.
- `to_json`/`from_json` on `Report`, `Contract` and `Refresh`.
- `Route.cls`, and the class values `exact`, `observed`, `shim`, `refused`.
- `storage_options`, `app_id` and the format-specific maintenance names
  (delta-rs's and Delta's terms; E3 only aligns `maintain`).
- `from_files`, `from_frame`, `from_query` and `sink_from` for custom
  sources and sinks.
- `assert_contract(engine=)` and `assert_engines_agree(engines=)` (G2), and
  the pytest fixtures `sv_source` and `sv_engine`.
- The CLI's `file.py:node` targets (the `module:attr` form of uvicorn and
  gunicorn), `--memory-limit` (DuckDB's `memory_limit`, with its `2GB`
  syntax), `--version`, and subcommand-local options.
- Exception attributes: `VerificationError.report`, `RouteError.route`,
  `PreconditionError.source`, `.condition` and `.rows`.
- A synchronous API.
- ODCS: keep sverify's names and map them in the export (L4).

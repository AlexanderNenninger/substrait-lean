# Changelog

## 0.9.0 (2026-11-23)

Known issue: a `RANK`, a top-n or a window partition over a double `SUM` or `AVG` can be reported proved on Polars and Spark, although the engine may order near-equal sums differently ([#2573](https://github.com/AlexanderNenninger/substrait-lean/issues/2573)). It is present since 0.8.0, and the fix is planned for 0.9.1.

The last release before 1.0's candidate: the public API has one name for each concept, with no deprecated aliases, the exit codes run from the best to the worst, each engine is an extra of its own, and every format sverify writes is bumped once. "Breaking changes" collects what a job has to change, and the breaking entries follow it, before the others.

### Breaking changes

This list says what an upgrade from 0.8.0 changes in a job, and the breaking entries after it give each change with its migration note. 0.9.0 keeps no deprecated alias. A renamed or removed name raises `AttributeError`, `TypeError` or `ImportError`, and the formats Sverify reads back read their earlier versions too ([stability.md](docs/stability.md)).

#### Install

- `pip install sverify` installs no engine to run plans on, DuckDB included.
  Add the engine you run: `sverify[duckdb]`, `sverify[polars]`,
  `sverify[spark]`, or `sverify[all]`. `sv.verify`, the SQL dialects and
  `report.to_sql` work without one.
- Each engine package covers the minor release its facts were probed at:
  `duckdb>=2.0.0,<2.1`, `polars>=2.1.0,<2.2`, `pyspark>=4.3.0,<4.4`. A run on
  another patch of that minor warns (`EngineVersionWarning`); a run on
  another minor raises `EngineVersionError`.
- Python 3.12 or later.
- `sverify-dbt` is released at the same version and pins `sverify==<version>`.

#### Command line

The exit codes run from the best to the worst, so the worst of several runs
is their maximum. `sverify.cli.ExitCode` names them:

| Outcome | 0.8.0 | 0.9.0 |
|---|---|---|
| proved | 0 | 0 |
| not proved | 1 | 1 |
| usage | 2 | 2 |
| unsupported | 3 | 3 |
| refused: no route to the engine | 3 (with unsupported) | 4 |
| budget exceeded | 4 | 5 |
| quarantined | 5 | 6 |
| held | 5 (with quarantined) | 7 |
| error | 6 | 8 |

- `--json` and `--output-format` are removed: write `--format json`, or
  `--format X`.
- `sverify contract export` drops `--format odcs`.
- `check --require-proved` exits 1 for a node whose postconditions are only
  checked on the data.
- `sverify check query.sql --schema schemas.yaml` checks a bare SQL file.

#### Python names

Old → new, with no alias. "One name for each concept in the public API" below has the
complete list, and "Breaking: deprecated aliases are removed" and "The deprecated
names are gone" the removals.

| 0.8.0 | 0.9.0 |
|---|---|
| `Report.proved` | `Report.verdict`, a `sverify.Verdict` |
| `sverify.types.Observation` | `sverify.types.Lenses` |
| `sverify.types.CheckedCondition` | `sverify.types.Postcondition` |
| `sverify.types.RefreshReport` | `sverify.types.BatchRefresh` |
| `SqlError`, `OdcsContract`, `SqlFrontEnd` | `SQLError`, `ODCSContract`, `SQLFrontEnd` |
| `Issue.hint_needs`, `Issue.suggested` | `Issue.suggested_requires`, `Issue.needs` |
| `CheckedCondition.suggested` | `Postcondition.needs` |
| `Route.kind`, `.reason`, `.facts`, `.proved_facts`, `.version` | `Route.taken`, `.why`, `.engine_facts`, `.theorem_facts`, `.probed_version` |
| `Contract.profile`, `Stored.profile` | `semantics` |
| `Stored.where`, `Stored.where_key` | `location`, `location_key` |
| `SinkWrite.inserted`, `.deleted` | `inserts`, `deletes` |
| `SourceBatch.trusted`, `.kind` | `assumes`, `mode` |
| `RetentionReport.view` | `RetentionReport.node` |
| `FlightSource(secret=)`, `FlightSource(token=)` | `FlightSource(credentials=)` |
| `Upstream.why_unverified`, `Upstream.evidence` | `Upstream.why`, `Upstream.assertions` |
| `sverify.engines.run(con, plan_json)` | `run(con, plan)` |
| `sverify.from_substrait`, `substrait_export.recheck` | `sverify.Report.from_substrait` |
| `sverify.Changes` | `sverify.io.Changes` |
| `from sverify.contracts import unique, Report, ...` | `sverify` and `sverify.types` |
| `sverify.io.FlightLog` | `sverify.testing.FlightLog` |
| `Sink.committed()` | `Sink.contract(version=None)` |
| `sverify.errors.Unsupported`, `NotIncremental` | `UnsupportedError`, `NotIncrementalError` |
| `Connection.arrow`, `Connection.ibis` | `con.get`, `con.rows`, `con.put`; `con.table(name).get_backend()` |
| `.last_report` | `.report` |
| `deterministic=` | `reproducible=sv.equivalent()` |
| `run_sharded(float_order="any")` | `run_sharded(reproducible=sv.equivalent(floats="plan"))` |
| `sv.sql(query, as_=)` | `sv.sql(query, name=)` |
| `arrives_within(col, days=, ...)` | `arrives_within(col, within)` |
| `rows_per(["a", "b"], 3)` | `rows_per("a", "b", at_most=3)` |
| `SVERIFY_CHECK`, `SVERIFY_PREBUILT_CHECK`, `SVERIFY_SPILL_DIRECTORY` | `SVERIFY_CHECKER`, `SVERIFY_PREBUILT_CHECKER`, `SVERIFY_TEMP_DIRECTORY` |

`bool(report.verdict)` raises `TypeError`: compare with the verdict you
expect. `SinkChange` takes keywords, and
`RefreshReport.diffed` is a dict of node to reason.

#### Defaults that changed

- Checks on data run the proved plan on the engine of the table's
  connection, where they went through Ibis. A condition outside the model
  now raises `UnsupportedError`. Sverify's own DuckDB connections, those of
  `sv.connect()` among them, run at the time zone UTC.
- `Report.run` runs the rewritten plan where one of seven proved rewrites
  applies and the preconditions were checked on the data;
  `run(optimize=False)` keeps the plan as written.
- The default observation reads `-0.0` and `0.0` as one value, every NaN as
  one, and a list's elements as a multiset; `elements="sequence"` observes
  their order.
- `Report.run` compares each table it reads with the schema the plan was
  verified for, and refuses a mismatch before a row is read.
- Under `semantics="reference"`, DuckDB SQL's `CAST(x AS <integer>)` of a
  double or a decimal is refused, since DuckDB rounds where the reference
  truncated: write `CAST(round(x) AS BIGINT)`, `floor` or `ceil`.
- A Polars or Spark run no longer runs the plan on DuckDB first, and
  `requires` are checked on the run's own engine.

#### Formats

Each changed format is bumped once. Sverify reads the earlier versions of
the formats it reads back ([stability.md, The formats](docs/stability.md#the-formats)).

| Format | 0.8.0 | 0.9.0 | What changed |
|---|---|---|---|
| Report JSON | 2 | 5 | `verdict`; `lenses`; a route's keys renamed as in the Python API |
| Sink contract record | 2 | 3 | `profile` is `semantics` |
| Substrait export manifest | 2 | 3 | follows `Report.lenses` |
| OpenLineage facet `sverify_contract` | 1 | 3 | follows `Report.lenses`; a route's `kind` is `taken` |
| Command line JSON | 1 | 2 | a write's `inserts` and `deletes`; a fix's `why` |
| Refresh report JSON | 1 | 2 | as the command line's |
| Quarantine record | 1 | 1 | unchanged |

A job that reads the command line's or the refresh report's JSON reads the
new keys.

#### sverify-dbt

- `sverify-dbt check --format json` prints the envelope of
  `sverify check --format json`; its models are `items`.
- It exits as `sverify check` does, and its `--fail-on` levels nest:
  `contract`, `unproved`, `refused`.
- Statuses are snake_case (`"not_proved"`, `"not_checked"`),
  `sverify_dbt.Needed` is `NeededTest`, and `CheckResult.proved` is
  `proved_tests`.


### Breaking: the default observation reads one zero and list elements as a multiset

Where `ensures` names no observation (`Report.lenses`, a sink's `reproducible`), `-0.0` now equals `0.0` and every NaN equals every other (`zeros="canon"`), and the order of a list's elements is not observed (`elements="multiset"`), as the order of rows is not ([#1285](https://github.com/AlexanderNenninger/substrait-lean/issues/1285), [the default observation](docs/core-semantics.md#the-default-observation)). Engines then run a plan as written where only the sign of a zero differs, with no zero-sign shim (`DuckDB`'s `round(-0.4)` may return `-0.0`); a contract that observes the signs (`sv.equivalent(floats="plan")` names zeros exact) keeps the shim. The order of elements counts with `elements="sequence"`; an `ORDER BY` inside the aggregate is what makes it determined there, and it does not raise the level. Every list is read as a multiset under the default, also one whose order the plan fixes (a literal, a sorted list, a split). `Report.observation` and its JSON (`equivalence`) show the new levels, so a report stored before reads as the new default where it carried none. A contract that names `sv.equivalent(...)` keeps every component it does not name exact, as before. The checker reads `elements="multiset"` for `Report.deterministic` in a follow-up: until then an unordered `collect` still reports a tie place. An unordered `string_agg` is one at every observation, since its value is a string.

### Breaking for raw SQL: an integer cast of a double under the default semantics

Under the default semantics (`"portable"`), `CAST(x AS <integer>)` of a double in DuckDB SQL is refused by the lift ([D54](docs/decisions.md#d54-the-lift-refines-the-dialect), #1484), where it truncated and DuckDB rounds half to even. Write `CAST(round(x) AS BIGINT)`, `CAST(floor(x) AS BIGINT)` or `CAST(ceil(x) AS BIGINT)`, which mean the same on both; the error names them. A decimal's cast lifts as DuckDB rounds it, half away from zero (#322). The Ibis frontend's cast still truncates (R9).

`Report.dialect_differences` lists where the reference reads a DuckDB SQL text differently from DuckDB on a value and the lift does not refuse it: `corr` of one pair or of a side whose values are all equal (NULL here, NaN on DuckDB). Each entry has the construct, where it is, both readings, an example and the spellings that mean the same. `str(report)` prints them as notes, `to_json` carries them, and the verdict is unchanged. The list is empty under `semantics="duckdb"` and for an Ibis transformation.

### `Report.verdict` replaces `Report.proved` (breaking)

`Report.proved`, a boolean, is removed with no alias. `Report.verdict` is a `sverify.Verdict`: `proved` (every postcondition holds and no run raises), `proved_with_checks` (the same, but a run stops where a check of `Report.assumed` fails on the data) or `unproved`. `bool(report.verdict)` raises `TypeError`, so `assert report.verdict` cannot pass on `unproved`; compare with the value you expect. `Report.run` and `on_unproved` treat both proved values as the old `proved`. `Postcondition.proved` stays a boolean. The report's JSON holds the value in `verdict` (format 2 held the first line of `str(report)`, which `summary` holds now), and `proved` stays, derived from `verdict`, until 2.0. The report's JSON is format 5 in this release, and `Report.from_json` reads formats 2 to 4. sverify-dbt's `CheckResult.proved` (a list) is renamed `proved_tests` for one name per concept ([#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484), finding 6).

### Breaking: `Sink.keeps_retired` is a plain class attribute (#2081)

`keeps_retired` is the one name a custom sink sets to say it keeps the rows a
view retires (`keeps_retired = True`). The deprecated property that read the
internal `_keeps_retired` is removed; nothing changes for a sink that already
sets `keeps_retired`.

### `semantics="portable"`, and lenses in the report's words

Breaking. The semantics every engine reaches is called `"portable"`:
`sv.verify(..., semantics="portable")` is the default, `Report.semantics`
and a route's `profile` say `"portable"`, and `sv.sql(..., semantics=...)`
takes `"duckdb"` or `"portable"`. `"reference"` is refused, with the list of
names `verify` takes. The reference profile keeps its name in the theory
(`Profile.reference`, `docs/core-semantics.md`). The SQL lift's profile
constant `sverify.sql_lift.REFERENCE` is `PORTABLE`.

Reports, Substrait manifests and sinks' contract records written before
1.0 say `"reference"`, and read as `"portable"`: a sink resumes, and its
plan's digest is unchanged ([docs/stability.md](docs/stability.md)).

Messages say "lenses" where they said "the observation": "no engine
meets the lenses' tolerance", "depends on floats, which the lenses ignore".
([#2081](https://github.com/AlexanderNenninger/substrait-lean/issues/2081),
[#1288](https://github.com/AlexanderNenninger/substrait-lean/issues/1288))

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
| `FlightSource(token=)` | `FlightSource(credentials=...)` |
| `run_sharded(float_order="any")` | `run_sharded(reproducible=sv.equivalent(floats="plan"))` |
| `sv.sql(query, as_=...)` | `sv.sql(query, name=...)` |
| `arrives_within(col, days=, hours=, minutes=, seconds=)` | `arrives_within(col, within)`, a `timedelta` or ISO 8601 duration |
| `rows_per(["a", "b"], 3)` | `rows_per("a", "b", at_most=3)` |
| `SVERIFY_PREBUILT_CHECK` | `SVERIFY_PREBUILT_CHECKER` |

The remaining aliases (`errors.Unsupported`, `Connection.arrow`, the
environment variables of the checker and the spill directory, and others) are
removed too, in "The deprecated names are gone".

### Composite foreign keys

`sv.references` takes several columns, as `sv.key` does:
`sv.references("street", "zip", to=[addresses.street, addresses.zip])`, or
`to=("addresses", ["street", "zip"])`. A row whose parts are all non-NULL
must match one row of the referenced table on every part (SQL's MATCH
SIMPLE). The data check, `sv.testing.cases`, the Substrait export and the
ODCS export and read handle it, and `odcs.read` now reads composite
relationships ([#2223](https://github.com/AlexanderNenninger/substrait-lean/issues/2223)).

A pair of columns that do not compare is refused at `verify`, for one column too.

Breaking: `References` has the fields `cols`, `table` and `others` (tuples),
in place of `col` and `other`. A report exported before this change reads back
only once exported again.

### Checks on data run the proved plan by default (breaking)

A check of `requires` on bound inputs, of `on_unproved="check"` on an output, of a batch at a refresh and of `Report.check_inputs` now runs each condition's plan, as the checker wrote it, on the engine of the table's `sverify.connect()` connection when no engine is named (`check_engine=None`), where it went through Ibis ([F219](docs/ledger.md#f219), [#2342](https://github.com/AlexanderNenninger/substrait-lean/issues/2342)). The count then has the reference's meaning on every engine. A condition outside the Lean model, which Ibis evaluated before, now raises `UnsupportedError` with the reason: write it in the subset `verify` reads. A table of another Ibis backend is still checked by Ibis there.

sverify's own DuckDB connections use the time zone UTC, so an instant (a UTC-zoned timestamp) comes back zoned UTC on a host in another zone. It used to come back in the host's zone, which the written plans refuse. A connection from `sv.connect()` is one of them: raw SQL run on it now runs at the time zone UTC, which shows where a `TIMESTAMPTZ` becomes text or a calendar value. Your own DuckDB connections keep theirs.

### `RefreshReport` is `BatchRefresh`, and `SinkChange` takes keywords (breaking)

`sverify.types.RefreshReport`, what one batch did to a node's state (`StageRefresh.report`), is renamed `BatchRefresh`, beside `Refresh`, `StageRefresh` and `SourceRefresh`, with no alias: `Report` names a verification only. `SinkChange` takes its arguments by keyword, like the other result types; a custom sink reads one and never builds it, so only a test that builds one changes (`SinkChange(view=..., contract=..., schema=..., change=...)`). `docs/stability.md` says that `sv.connect()` returns a `sverify.engines.Connection`, and the engines guide pairs `semantics=` with `engine=` ([#2343](https://github.com/AlexanderNenninger/substrait-lean/issues/2343)).

### `Report.from_substrait` is the one way to read a stored plan back (breaking)

`sverify.substrait_export.recheck` and `sverify.substrait_export.from_substrait` are removed with no alias: `sv.Report.from_substrait(data)` reads an export and proves its contract again, as before ([#2344](https://github.com/AlexanderNenninger/substrait-lean/issues/2344)).

### One name for each concept in the public API (breaking)

The 1.0 naming sweep ([#2345](https://github.com/AlexanderNenninger/substrait-lean/issues/2345), ruling 263) gives each concept one name across the Python API, the formats and the command line. No old name stays as an alias: each raises `AttributeError`, `TypeError` or `ImportError`, or is a key a reader of the new format maps. A `reason` is a code and `why` is words, in the Python API and the JSON sverify writes per run; a stored table's columns and record keys keep their names, so the quarantine table's `_reason` and its record's `reason` stay (`docs/stability.md`, ruling 264).

Python names, old → new:

- `sverify.types.Observation` → `sverify.types.Lenses`, as `Report.lenses` names it.
- `sverify.types.CheckedCondition` (the items of `Report.ensures`) → `sverify.types.Postcondition`: "check" reads data (F219).
- `sverify.errors.SqlError` → `SQLError`, `sverify.odcs.OdcsContract` → `ODCSContract` and `sverify.profiles.SqlFrontEnd` → `SQLFrontEnd`: an acronym is capitals in a public name, as in `SQLStep`.
- `Issue.hint_needs` → `Issue.suggested_requires`, as `Report.suggested_requires`.
- `Route.kind` → `Route.taken`; `Route.reason` → `Route.why`; `Route.facts` → `Route.engine_facts`; `Route.proved_facts` → `Route.theorem_facts`; `Route.version` → `Route.probed_version`, beside `Route.unprobed_version`.
- `sverify.io.Contract.profile` and `Stored.profile` → `semantics`, as `Report.semantics`.
- `Stored.where` and `Stored.where_key` → `location` and `location_key`, as `Sink(location=)`.
- `SinkWrite.inserted` and `SinkWrite.deleted` → `inserts` and `deletes`, as `SourceRefresh`.
- `SourceBatch.trusted` → `assumes`, as `Source(assumes=)`, and `SourceBatch.kind` → `mode`, as `SourceRefresh.mode`; `SourceBatch.from_changes(trusted=, kind=)` → `(assumes=, mode=)`, and `SourceBatch.from_snapshot(reason=)` → `(why=)`.
- `RetentionReport.view` → `RetentionReport.node`.
- `FlightSource(secret=)` → `FlightSource(credentials=)`, as every other source. The token is now named in the refresh's `credentials`, as every source's are.
- `sverify.odcs.Unread.reason` → `Unread.why`.
- `sverify.openlineage.Upstream.why_unverified` → `Upstream.why`, and `Upstream.evidence` → `Upstream.assertions`.
- `sverify.engines.run(con, plan_json, ...)` → `run(con, plan, ...)`, as `run_sharded(plan, ...)`.
- `Postcondition.checker_ignores`, `Report.check_asof_pairs` and `Report.check_margins` are internal now: `Postcondition.ignores` is the public view, and `Report.run` calls the other two.

Formats, each bumped once; the two that sverify reads back, the report and the sink record, are read in their earlier formats too:

- The report's JSON is format 5. A route's keys `kind`, `reason`, `facts`, `version` and `proved_facts` are `taken`, `why`, `engine_facts`, `probed_version` and `theorem_facts`. `Report.from_json` reads formats 2 to 4.
- The sink's contract record is format 3. Its key `profile` is `semantics`. `Contract.from_json` reads formats 1 and 2.
- The OpenLineage facet `sverify_contract` is format 3. Its route's `kind` is `taken`, as in the report JSON; its `_schemaURL` is `…/schemas/openlineage-contract-facet/3.json`.
- The command line's JSON is format 2, and the refresh report's JSON (`Refresh.to_json`) is format 2. A write's `inserted` and `deleted` are `inserts` and `deletes`, and in the command line's JSON a fix's `reason` (`check --fix`, `--diff`) is `why`. The refresh report's `$schema` is `…/schemas/refresh/2.json`. Jobs that read these documents read the new keys.

Command line: `--json` is removed. Write `--format json`. `sverify-dbt check --format json` writes format 2 of the same document.

Messages follow the names. A refresh that finds the stored state verified under other semantics says "the plan was verified under semantics='duckdb', and is now under semantics='portable'", and `sverify check --against-sink` says "(semantics='portable' then, 'duckdb' now)". A retention line names the node.

### `sverify.contracts` re-exports nothing (breaking for its imports)

`sverify.contracts` is internal, and it no longer re-exports the 40 names it took from `sverify.conditions` and `sverify.report`. An import such as `from sverify.contracts import unique, Report` raises `ImportError`. Import from the public modules: `sverify` (`sv.unique`, `sv.max_rows`, `sv.references`, `sv.rows_per`, `sv.arrives_within`, `sv.approx`, `sv.Report`) and `sverify.types` (the condition and report types, such as `Unique`, `Needed`, `Issue`). `docs/stability.md` lists the public modules ([#2410](https://github.com/AlexanderNenninger/substrait-lean/pull/2410), [#2081](https://github.com/AlexanderNenninger/substrait-lean/issues/2081)).

### Breaking: exit codes run from the best to the worst (#2458)

`sverify check`, `refresh` and `explain` (and the `exit` of their JSON) number
their exit codes by severity, so the worst of several runs is their maximum.
`sverify.cli.ExitCode` names them, and `sverify-dbt` and the pipeline
template's `lake.py` read it.

| Outcome | 0.8.0 | Now |
|---|---|---|
| proved | 0 | 0 |
| not proved | 1 | 1 |
| usage | 2 | 2 |
| unsupported | 3 | 3 |
| refused (no route to the engine) | 3 (with unsupported) | 4 |
| budget exceeded | 4 | 5 |
| quarantined | 5 | 6 |
| held | 5 (with quarantined) | 7 |
| error | 6 | 8 |

### Status names each node's mode and why it recomputes (breaking: `RefreshReport.diffed`)

`Status` and the refresh report name how each node is maintained: "delta rules", "state per group", "touched groups", "touched frames" or "recompute and diff". A node that is recomputed and diffed says which operator causes it, in `NodeStatus.recomputed` and in the refresh summary. `RefreshReport.diffed` changes from a list of view names to a dict of view to reason: indexing and `.append` no longer work, iteration, truthiness and `len` do (#742).

### Breaking: two more exit codes; `check --require-proved`; relaxations in the JSON (#881 S1, S2, 1.3)

- `sverify` exits 3 only for a construct outside the model. A proved node with
  no route to the engine (`refresh`) exits 4, `status` `"refused"`. A refresh
  that held a node exits 7, `status` `"held"`; 6 is for rows quarantined.
  `cli.schema.json` allows `exit` up to 8, and the codes run from the best to the
  worst (#2458).
- `sverify check --require-proved` exits 1 for a node whose unproved
  postconditions are only checked on the data (`on_unproved="check"`), with a
  `checked_only` finding that `sverify explain` describes. The pipeline
  template's check workflow passes it.
- Each item of the JSON has `relaxations`, the settings of its transform that
  weaken the gate (`on_unproved="check"`, `on_inferred="ignore"`, `"off"` or
  `"warn"`, `check_requires=False`), for a CI step to diff between base and head.
- A report's text for an assumed-finite operation says the plan raises and
  commits nothing on overflow, where it said the data is refused before the run.
- `docs/stability.md` says what the promise covers of the checker binary.

### Breaking: `--output-format` removed (#881 S5)

`sverify` and `sverify-dbt check` take `--format`. Replace
`--output-format X` with `--format X`. `sverify` no longer takes `--json`
("One name for each concept in the public API"); `sverify-dbt check` still does.

### `Report.needs` is the one name; result and IO dataclasses are keyword-only

Breaking. `Report.needed`, `Report.needed_text` and `Report.needed_conditions`
are removed: read `Report.needs` (`Needed.label`, `.text`, `.condition`). The
old names of `Report`'s internal fields (`depends`, `epsilon`, `transfer` and
the 28 others) and `Report.plan` (`Report.internal_plan`) no longer read with
a `DeprecationWarning`; 1.0 keeps no alias
([#2081](https://github.com/AlexanderNenninger/substrait-lean/issues/2081)).

`Report`, `Contract`, `Batch`, `Snapshot`, `SourceBatch` and `SinkWrite` take
keyword arguments only, so a field added in 1.x breaks no caller. sverify
builds `Report` and `Contract`; a source or sink of your own builds the other
four, by keyword: `Batch(table=rows, cursor=n)`.

`sverify.odcs.UnreadRuleWarning` and `sverify.openlineage.LineageWarning`
derive from `SverifyWarning`, so `warnings.simplefilter("error",
SverifyWarning)` covers every warning sverify gives.

A precondition checked on data with `check_engine=` counts the rows that
break it inside the engine: 8 ms on 5 million rows on DuckDB, where it took
187 ms
([#881](https://github.com/AlexanderNenninger/substrait-lean/issues/881)).

### One verb for proving, and the plan layer in a module of its own

Breaking.

- `ContractedTransform.check(...)` is `ContractedTransform.verify(...)`: "verify"
  proves (`sv.verify`, `.verify`), and "check" reads data (`check_requires`,
  `Report.check_inputs`, `proved_with_checks`). The commands keep their names:
  `sverify check` and `sverify-dbt check` verify a project.
- `on_unproved="runtime"` is refused; write `on_unproved="check"`.
- The plan layer moved to `sverify.engines.plan`, outside the 1.x promise:
  `to_sql`, `substrait_json`, `written_plan` and `delta_plans`. Import them
  from there; `sverify.engines` no longer has them. `sverify.engines.create_table`
  and `table_rows` are gone (`con.create`, `con.rows`), and so is
  `sverify.engines.Unsupported` (`UnsupportedError`).
- `sverify.errors` says which exceptions keep a built-in base, and the bases
  are fixed for 1.x.
- `sverify check --fix` and `--diff` say that the preconditions they write
  narrow the input each node accepts.

([#881](https://github.com/AlexanderNenninger/substrait-lean/issues/881))

### Breaking: sverify-dbt prints sverify's JSON document, and takes only sverify's public API

`sverify-dbt check --format json` prints the envelope of `sverify check --format json` (`format`, `sverify`, `command`, `exit`, `status`, `items`, `findings`, `error`), with the dbt version and adapter beside it. The models are now `items`, no longer `models`: a script reading `.models` must read `.items`. Each model is an item (`status` `refused` for a model sverify cannot read, added to the schema) and each unproved test a finding with sverify's code, which `sverify explain` takes. A failed check prints the envelope with its `error` as well. sverify-dbt catches `UnsupportedError` for a refusal instead of every `ValueError`, and a test lists the few names it still takes outside the public API ([#891](https://github.com/AlexanderNenninger/substrait-lean/issues/891)).

### sverify-dbt's result types take keywords and say statuses in snake_case (breaking)

Before 1.0 freezes them ([#891](https://github.com/AlexanderNenninger/substrait-lean/issues/891) 2.6), sverify-dbt's result types match sverify's. No old name stays as an alias.

- A test's or constraint's `status` is `"pending"`, `"proved"`, `"not_proved"` or `"not_checked"` (`sverify_dbt.result.Status`), where it was `"not proved"` and `"not checked"`. This holds in `TestResult.status`, `ModelResult.by_status(...)` and the tests of each item in `sverify-dbt check --format json`. The text report keeps its words.
- `sverify_dbt.Needed` is `NeededTest`, since `sverify.types.Needed` is another class, and its `because` is `why`.
- `Suggestion.because` (from `CheckResult.suggestions()`) is `Suggestion.why`, a `list[str]`.
- `TestResult`, `NeededTest`, `ContractIssue`, `ModelResult`, `CheckResult` and `Suggestion` take keyword arguments only.
- `CheckResult.tests` and `CheckResult.relations`, the manifest's nodes, are internal (`_tests`, `_relations`).

### A postcondition that reads an unbounded double is refused with its exit

A route to an engine ran a postcondition that read a double with no bound on its distance to the reference (a mean or `SUM` without a row cap) while refusing the same postcondition on a double with a bound, so `avg <= 100` ran uncapped and was refused with `sv.max_rows(1000)`. The checker's engine-robustness now keeps only the sign of such a column, and the route refuses what reads more, naming `sv.approx(...)` and the row cap. What reads only the sign (`_.total >= 0`) runs as before ([#1045](https://github.com/AlexanderNenninger/substrait-lean/issues/1045)).

### Routes, profiles and typed values in the tour

An explicit `route=` that does not apply now names how to reach the engine: verify under `semantics="reference"`, or pass `route="auto"` ([#1046](https://github.com/AlexanderNenninger/substrait-lean/issues/1046)). The tour shows `semantics="polars"` and the refusal ([chapter 5](notebooks/05_pipelines_and_engines.py)) and a decimal's scale and an unsigned column's refusal ([chapter 4](notebooks/04_contracts.py), [#1050](https://github.com/AlexanderNenninger/substrait-lean/issues/1050)). `docs/proofs.md` names the theorem each route and class rests on.

### A tour chapter on engines

The tour has a seventh notebook, [Engines](notebooks/07_engines.py): one proved plan runs on DuckDB, Polars and Spark, its routes are read, the plan is written as Spark SQL, and two refusals are followed to their exits ([#1047](https://github.com/AlexanderNenninger/substrait-lean/issues/1047)).

### Two more refusals name their exit

A Delta sink whose table has constraints the view does not guarantee says to add them to the view's `ensures` or drop them from the table; an incremental view over preconditions that were not proved says to state them in the `ensures` of the transformation that produces those inputs
([#1048](https://github.com/AlexanderNenninger/substrait-lean/issues/1048), [#1051](https://github.com/AlexanderNenninger/substrait-lean/issues/1051)).

### Contracts, export and sinks in the tour

Chapter 4 shows `sv.rows_per` beside `sv.max_rows` ([#1057](https://github.com/AlexanderNenninger/substrait-lean/issues/1057)), chapter 5 stores a sum of doubles under exact bits and under a tolerance ([#1048](https://github.com/AlexanderNenninger/substrait-lean/issues/1048)), and `docs/getting-started.md` says what the Substrait export rests on ([#1053](https://github.com/AlexanderNenninger/substrait-lean/issues/1053)). `docs/teaching.md` lists each answer.

### A tour chapter on sverify-dbt

The tour has an eighth notebook, [Your dbt project](notebooks/08_dbt.py): a small dbt project is compiled and checked with `sverify_dbt.check`, a test it cannot prove is read through its counterexample and fixed in the model, the proved tests go into a selector for `dbt build`, and two refusals are followed to their exits. The published notebooks pin `sverify-dbt` to the release with `sverify` ([#1055](https://github.com/AlexanderNenninger/substrait-lean/issues/1055)).

### Refusals of data and composition name their exit

A composition that fails now ends with "state it in the producer's `ensures`, or set `on_unproved="check"`"; data that breaks a key, a row cap or a stated precondition names `on_violation="quarantine"` or `"hold"`; the CLI's time-budget message names `--timeout` and `SVERIFY_TIMEOUT`
([#1056](https://github.com/AlexanderNenninger/substrait-lean/issues/1056), [#1057](https://github.com/AlexanderNenninger/substrait-lean/issues/1057)).

### One place decides "proved"

`Report` alone combines a report's fields into "proved"; the CLI's status of a
discovered transform and the Substrait export now call it. The trusted-base
page lists that decision and every read after it, and a test fails where
another module starts deciding for itself
([#1088](https://github.com/AlexanderNenninger/substrait-lean/issues/1088)).

### How this project is built

`docs/how-this-is-built.md` says who writes and checks the project, what you can check without trusting anyone, where a person's judgement enters, how a change lands and how to disagree. The READMEs link it ([#1089](https://github.com/AlexanderNenninger/substrait-lean/issues/1089)).

### Upstream report lists what is filed and fixed

`upstream/REPORT.md` has a "Filed and fixed" table with each thread's link, the release that fixes it and how sverify handles it, the README links it, and CI warns when an open upstream thread has gone 90 days without a check ([#1091](https://github.com/AlexanderNenninger/substrait-lean/issues/1091)).

### Theorem cards for the three engine soundness theorems

`docs/theorems/duckdb_sound.md`, `polars_sound.md` and `spark_sound.md` say what each engine theorem assumes and leaves out, with examples whose routes and theorem names `test_readme.py` pins ([#1094](https://github.com/AlexanderNenninger/substrait-lean/issues/1094)).

### Theorem cards for `floatSumCR_mem`, `floatAvgCR_mem` and `comomentNum_nonneg`

The last cards of [#1094](https://github.com/AlexanderNenninger/substrait-lean/issues/1094): the bounds of a `SUM` and an `AVG` of doubles and the non-negative variance numerator, with examples whose verdicts `test_readme.py` pins. Every top-level theorem the issue lists has a card.

### Theorem card for `Rel.keys_sound`

`docs/theorems/keys_sound.md` says what a derived key means, what it assumes and what it leaves out, with three examples whose verdicts `test_readme.py` pins. `dbt/README.md` links it with `contract_sound` ([#1094](https://github.com/AlexanderNenninger/substrait-lean/issues/1094)).

### Theorem cards for `Rel.AllowedP_mono`, `Rel.refines_of_perm` and `Rel.optimize_refines`

Three more cards in `docs/theorems/`, each with an example whose verdict, route or rows `test_readme.py` pins ([#1094](https://github.com/AlexanderNenninger/substrait-lean/issues/1094)).

### Theorem cards for the refresh protocol

`docs/theorems/` has cards for `Refresh.no_corruption`, `Refresh.record_describes_table`, `Refresh.read_is_head`, `Refresh.monotone` and `Refresh.quiet`. They say what each assumes and leaves out; the first two have a Delta example whose summaries `test_readme.py` pins: a resumed refresh, a merge, and a replace after another application wrote the sink ([#1094](https://github.com/AlexanderNenninger/substrait-lean/issues/1094)).

### Theorem cards

`docs/theorems/` has a page for each theorem of the contract family (`contract_sound`, `contract_sound_all`, `contract_sound_allowed`, `contract_sound_allowed_closed`): what it says, what it assumes, the Lean statement line by line, what it rules out and doesn't cover, and an example that runs in CI ([#1094](https://github.com/AlexanderNenninger/substrait-lean/issues/1094)).

### `AND` and `OR` guard the next operand (D50)

`WHERE qty <> 0 AND total / qty > 1` is now proved: the SQL and Ibis frontends
lift an `AND` or `OR` over a raising operand so the operand runs only where the
earlier ones do not decide the result. `semantics="duckdb"` keeps DuckDB's
eager reading.

### A run records the engine settings it was checked under

Each route now carries the engine settings its profile assumes, as read from the session the run uses (`Route.settings`, and `settings` in the report JSON), so a run's record says what it ran under. The Spark session sverify starts is read back against `SPARK_CONF` before it runs anything, and refused with `EngineSettingsError` where a setting did not take, as when Spark hands back a session the process already had. A test now holds that an engine that raises commits nothing to a Delta, Iceberg or custom sink ([#1130](https://github.com/AlexanderNenninger/substrait-lean/issues/1130)).

### DuckDB's Lean half, a Lake package of its own

DuckDB's functions under its settings, the SQL printer's model and its
soundness, the black boxes and the casts from VARCHAR, its choice table and
the lowering's lemmas move into `engines/duckdb/`, the Lake package
`sverify-duckdb` with modules `Sverify.DuckDB.*`, beside its Python
distribution ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
It builds on the core, the analysis and engines-common alone, and CI checks
that it does. The generated lowering, `Engine.duckdb` and the lift stay in
the root package until the generators move. No theorem changed.

### DuckDB's lowering joins its Lean package

The lowering generator (`generate_lowering`, `Sverify.Engines.LoweringSearch`)
moves into engines-common, and DuckDB's lowering, its generated entries, its
cache and `Engine.duckdb` into `sverify-duckdb`
([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
The package reads `check_generated` itself, and the root passes its own
setting on. The lift stays in the root package until its parser has a
package. No theorem changed.

### The frontend, a Lean package of its own

The Substrait JSON parser (`Parse`) and the builders of Substrait's JSON
(`SubstraitJson`) move into `frontend/`, the Lake package `sverify-frontend`
with modules `Sverify.Frontend.*`, which builds on the core and the analysis
alone ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
The lift from DuckDB's SQL (its generator, hints, cache and generated
entries) joins `sverify-duckdb`, which imports the frontend. DuckDB's Lean
half is now all in its package. No theorem changed.

### Polars's Lean half, a Lake package of its own

Polars's table, shims, profile and `Engine` value move into
`engines/polars/`, the Lake package `sverify-polars` with modules
`Sverify.Polars.*`, beside its Python distribution
([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
It builds on the core, the analysis and engines-common alone, and CI checks
that it does. No theorem changed.

### Polars's Lean modules stand on the shared packages

Polars's Lean modules now import only the core, the analysis, engines-common
and each other ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
The lowering machinery (`Sverify.Engines.Lowering`) and what an engine's
model is sound for (`Sverify.Engines.Sound`) join engines-common,
`Profile.reference_faithful` joins the analysis (`Sverify.Analysis.ProfileImpl`),
and `Expr.floorDivOf`/`Expr.floorModOf` join the core. Polars's table and
`Engine` value get modules of their own (`PolarsTables`, `PolarsEngine`). No
theorem changed.

### Spark's Lean half, a Lake package of its own

Spark's table, shims, profile and `Engine` value move into `engines/spark/`,
the Lake package `sverify-spark` with modules `Sverify.Spark.*`, beside its
Python distribution
([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
It builds on the core, the analysis and engines-common alone, and CI checks
that it does; it no longer imports Polars's shims. No theorem changed.

### Substrait's profile, a Lean package of its own

`Profile.substrait`, the YAMLs' own looseness, moves into `engines/substrait/`,
the Lake package `sverify-substrait` with modules `Sverify.Substrait.*`, on the
core alone ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
`verify(semantics="substrait")` is unchanged. With it, every engine's and
Substrait's Lean half is a package of its own. No theorem changed.

### The core's rounding is proved to meet the float bounds' standard model

The bounds in `float-bounds/` are proved for any rounding that meets the
standard model, and the core rounds with integer codes. A new library,
`float-bounds/FloatBridge`, proves that the core's rounding is such a model
and agrees with the codes on every value the core rounds
([#1196](https://github.com/AlexanderNenninger/substrait-lean/issues/1196)),
one step of the link between the two that was trusted.

### Kahan's sum and DuckDB's constant runs are proved within the sum bound

Sverify now proves the bound on an engine's double `SUM` for the last two
summation orders it took as given: Kahan's compensated sum (`COMPENSATED`,
Polars's grouped sums) and DuckDB's constant runs added as one product
(`SCALED_CONSTANT`). Both algorithms are written on the core's codes and
proved to meet `SumOrder` through the float-bounds bridge
(`KahanSums.sumOrder`, `FloatSumsK.sumOrder`,
[#1196](https://github.com/AlexanderNenninger/substrait-lean/issues/1196)).
What stays trusted is that the engine runs the algorithm its fact names.

### The Ibis producer's and the Substrait export's refusals say what to do

A construct the Ibis producer does not read ends with a rewrite ("rewrite it with a supported operation or column type"), and `to_substrait` refusals end with a fix: a malformed plan says to export one sverify produced, a missing checker feature to rebuild `substrait-check` from the same commit, an unverified report to fix what it names and verify again ([#1205](https://github.com/AlexanderNenninger/substrait-lean/issues/1205)).

### Five more refusals name what to do

An unparseable SQL model, a secret path without its mount or vault, a missing
secret-server address, an HTTP error from the secret server and a Snowflake
substring bound at 2^32 now end with the fix
([#1205](https://github.com/AlexanderNenninger/substrait-lean/issues/1205)).

### Ten more refusals say what to do

A HUGEINT literal, a `uuid` or other unsupported column type, a timestamp with a time zone, a list of decimals, `collect(include_null=True)`, truncating to a sub-second unit, a `VALUES` alias with too many names, a black-box call with the wrong argument count, an export with no matching Substrait impl and a streaming plan that falls back in memory under `streaming="require"` now end with the change that lifts them. `python -m sverify_dev.exits` counts the refusals that still name nothing (345 of 583); a test keeps the count from rising ([#1205](https://github.com/AlexanderNenninger/substrait-lean/issues/1205)).

### A refusal on Snowflake names its exit

A route refused because the checker cannot yet check under `semantics="snowflake"` now ends with the issue that lifts it ([#852](https://github.com/AlexanderNenninger/substrait-lean/issues/852)).

### The SQL lift's refusals say what to do

Each construct the SQL lift refuses now ends with something to do: a rewrite the lift reads (nine refusals about the query itself: an unresolved name, a table that is not an input, `HAVING` without `GROUP BY`, a misplaced or nested aggregate, a wrong argument count), or, for a construct it does not read yet, "write this step in Ibis", with the open issue that tracks the construct where there is one ([#319](https://github.com/AlexanderNenninger/substrait-lean/issues/319), [#322](https://github.com/AlexanderNenninger/substrait-lean/issues/322), [#342](https://github.com/AlexanderNenninger/substrait-lean/issues/342), [#348](https://github.com/AlexanderNenninger/substrait-lean/issues/348), [#350](https://github.com/AlexanderNenninger/substrait-lean/issues/350)). `python -m sverify_dev.exits` counts the refusals that still name nothing, and a test keeps the count from rising ([#1205](https://github.com/AlexanderNenninger/substrait-lean/issues/1205)).

### The SQL writer's refusals say what to do

A plan the SQL writer cannot write now ends with a fix or a way out: a malformed plan says to build it with sverify or fix it, and the other refusals say to rewrite the step or run the plan with another engine. `python -m sverify_dev.exits` counts the refusals that still name nothing, and a test keeps the count from rising ([#1205](https://github.com/AlexanderNenninger/substrait-lean/issues/1205)).

### `DECIMAL(38, 0) + DECIMAL(38, 0)` is typed

`verify` refused the sum of two `DECIMAL(38, 0)` columns because the inferred bound on them was a whole number past 64 bits, which reads as a HUGEINT. The bound is now a decimal literal, so the sum is typed as `DECIMAL(38, 0)` and its possible overflow is reported as an issue ([#1252](https://github.com/AlexanderNenninger/substrait-lean/issues/1252)).

### An Ibis table with a DuckDB ENUM column is refused

Ibis types a DuckDB `ENUM` as `string`, so a plan over an Ibis table bound to
a DuckDB backend was proved under text order, where DuckDB orders an `ENUM` by
declaration position
([#1253](https://github.com/AlexanderNenninger/substrait-lean/issues/1253)).
The DuckDB engine now reads the declared types of the base tables an Ibis
expression scans and refuses `UUID`, `ENUM`, `BIT` and `BIGNUM` columns with
the exit (`CAST(col AS VARCHAR)` in the source query). A plugin may set
`ProfilePlugin.refuse_declared_types` to do the same for its engine.

### DuckDB UUID, ENUM, BIT and BIGNUM columns are refused with their exit

Arrow exports a DuckDB `UUID` as text, and DuckDB compares a string with a
`UUID` by casting the string, so a plan read as text proved the wrong rows
([#1253](https://github.com/AlexanderNenninger/substrait-lean/issues/1253)).
Sverify now refuses a column by the type DuckDB declares for it, whatever
Arrow exports it as (`UUID`, `ENUM`, `BIT`, `BIGNUM`, also inside a list,
struct or map), and the message names the exit: read it as text with
`CAST(col AS VARCHAR)` in the source query. Three engine facts record what
DuckDB does (`duckdb-uuid-text-order`, `duckdb-uuid-string-cast`,
`duckdb-enum-order`).

### Polars tables no longer name a `column_divisor` shim

The Polars tables listed a `column_divisor` shim for `%` of doubles that nothing implemented. The row now says what the engine does: Polars refuses `%` of doubles until `Profile.polars` models the floored `%` ([#1270](https://github.com/AlexanderNenninger/substrait-lean/issues/1270)).

### Polars runs `%` of doubles natively under `semantics="polars"`

`Profile.polars` models Polars's `%` of doubles, `x - y * floor(x / y)` over Polars's own `/`, and the Polars engine runs it natively, for column and literal divisors alike ([#1270](https://github.com/AlexanderNenninger/substrait-lean/issues/1270), decision D41: `fp.mod` accepts `division_type: FLOOR`). A zero divisor and an infinite operand raise under the profile, where Polars gives NaN. Under the reference, `%` of doubles stays refused on Polars.

### Polars computes shifts, `ROUND` and `log(x, b)` natively

On Polars, `<<` and `>>`, `ROUND(x, d)` for `0 ≤ d ≤ 22` and `log(x, b)` run
as Polars expressions where they called Python per row or numpy per batch
([#1270](https://github.com/AlexanderNenninger/substrait-lean/issues/1270)).
The values are the same. On a million rows the shifts take 1 to 2 ms, down
from 56 to 109 ms.

### Polars runs no Python: `log10`, `log2` natively, five operations refused

Polars's translation no longer calls Python per row or numpy per batch for
what Polars cannot compute exactly
([#1270](https://github.com/AlexanderNenninger/substrait-lean/issues/1270)).
`log10` and `log2` run as Polars's own `ln(x) / ln(b)`, within 2.1 ulp of
libm's, which the plan's float bound states (polars-ulp-libm). On Polars these
are refused with the reason and another engine to run them on: `ROUND(x, d)`
outside `0 ≤ d ≤ 22`, `%` of doubles, `levenshtein`, and `replace`, `LIKE` and
`ILIKE` with a pattern that is not a literal. DuckDB and Spark run them as
before.

### Polars computes `replace`, `reverse`, `ascii`, `repeat` and `LIKE` natively

On Polars, `replace` with a literal pattern, `reverse`, `ascii`, `repeat`,
and `LIKE`/`ILIKE` with a literal pattern run as Polars expressions where they
called Python per row ([#1270](https://github.com/AlexanderNenninger/substrait-lean/issues/1270)).
The values are the same. On a million rows they take 1 to 29 ms, down from
97 to 184 ms. A pattern per row still takes the old path.

### Fixed: `rows="sequence"` needs a sort without ties

A postcondition that observes the rows as a sequence (`sv.equivalent(rows="sequence")`) used to run on an engine whenever the plan's result was sorted, also when the sort keys tied and the engines may order the ties differently. The checker now proves the sequence (`sequence_determined`, `check_sequence_determined_sound`) when the sort's columns contain a key of its input, none clustered, and the route refuses it otherwise. A contract that sorts on a non-key under `rows="sequence"` states a key (`sv.unique`) or observes `rows="ties permuted"` ([#1285](https://github.com/AlexanderNenninger/substrait-lean/issues/1285)).

### Added: `strings="casefold"` and `strings="ascii"`

`sv.equivalent(strings=...)` takes two more levels: `"casefold"` (Unicode's canonical caseless match) and `"ascii"` (the compatibility caseless match, keeping the code points below U+0080, so `søren` equals `sren`). The default stays `"exact"`. The levels are the ones Lean's `StringObs` has; [what they hide](docs/core-semantics.md#what-the-string-levels-hide) ([#1285](https://github.com/AlexanderNenninger/substrait-lean/issues/1285)).

### What "verified" means

The getting-started guide and `docs/core-semantics.md` say what a verified
plan is: proved, and determined up to its profile's observation, so every
sound engine gives the one answer
([#1285](https://github.com/AlexanderNenninger/substrait-lean/issues/1285)).

### Report: one name for what a proof needs, proved NOT NULL in the output types, the engine version

API changes, with no aliases ([#1288](https://github.com/AlexanderNenninger/substrait-lean/issues/1288) API-5):

- `CheckedCondition.suggested` (a mapping of conditions per table) is now `CheckedCondition.needs`, a tuple of `Needed` like `Report.needs` and `Issue.needs`. The report JSON writes each as a whole `needed` object, as it writes `Report.needs`.
- `Issue.suggested` is removed: read `Issue.needs`. `on_inferred="silent"` is refused with a `ValueError`: write `"ignore"`.
- `Report.facts` maps each column to a `ColumnFacts` (`nullable`, `lower`, `upper`; `str()` gives the words it held before), in the report JSON too ([#704](https://github.com/AlexanderNenninger/substrait-lean/issues/704)).
- `Report.suggestions` is removed: read `c.needs` of each `c` in `report.ensures`.
- `Report.lenses` is the one name for what the result's consumer observes: it replaces `Report.observation` and `Report.equivalence`, and `Route.observation` is `Route.lenses`. A postcondition whose `reason` was `"observation"` reads `"lenses"`, and `str(report)` prints a `lenses:` line.
- Three written formats follow the name, each with a new version; files written before still read:
  - the report's JSON, format 4: `lenses` for `equivalence` (in a route too), each of `facts` an object, and each of a postcondition's `needs` a whole `needed` object;
  - the Substrait contract manifest, format 3: `lenses`, `lenses_components` and an `up_to` entry's `lenses` for the `equivalence` names;
  - the OpenLineage facet `sverify_contract`, format 2 (its schema URL ends in `/2.json`): `lenses` for `equivalence`.
  A release older than this one refuses the new formats and says to upgrade.
- `Report.warnings` is removed. It was always empty; `report.issues` with `error` false is the same list.
- `Report.not_null` is removed: `Report.output` types each column the checker proves never NULL as not nullable (`count(*)` is `!int64`), so `[c for c, t in report.output.items() if not t.nullable]` is the list ([#704](https://github.com/AlexanderNenninger/substrait-lean/issues/704)). The report JSON keeps its `not_null` list, and a report written before reads back with those columns not nullable.

A postcondition proved only with a precondition sverify inferred is no longer reported as proved under `on_inferred="error"`: its `proved` is false, its `reason` is `"needs"` and its `needs` lists the bounds its proof used. A postcondition that holds without them stays proved; `Report.facts` and `Report.output` then rest on the stated preconditions alone. sverify-dbt still marks every test of a model that needs source tests as not proved, and says which tests used a bound and which hold but leave the model able to fail ([#701](https://github.com/AlexanderNenninger/substrait-lean/issues/701)).

`Report.engine_version` is the engine version the profile of `semantics` describes (`"2.0.0"` under `semantics="duckdb"`), None under the reference; the report JSON carries it ([#710](https://github.com/AlexanderNenninger/substrait-lean/issues/710)).

### A source's change log drops what every reader has read

`StaticSource` kept every change `apply` made since it was built, and an `io.Source` the last 64 batches, in the Python process, after every node had read them. A long-running pipeline's driver memory grew with its input, beside the views' state in the engine. Each pipeline now reports the version it committed, and the log keeps only the changes some reader has not read yet. A reader that lags keeps its changes; one older than the log gets the whole table to diff, as before (#1329).

### The checker names the columns a view reads

`substrait-check --reads plan.json` prints, for each table a plan reads, the columns its output needs, or `"all"` outside the incremental fragment. Sverify proves that a stored table keeping those columns, consolidated, gives the view and its delta plans (`Rel.zeval_prune`, `Rel.incremental_sound_prune`), so incremental refresh can store less of an input ([#1329](https://github.com/AlexanderNenninger/substrait-lean/issues/1329)). The checker speaks protocol 3: a sverify older than this checker refuses it with a message to upgrade.

### Polars keeps a pipeline view's state in Parquet parts, as Spark does

On Polars, a refresh now writes the change as a new Parquet part and leaves the state's other parts where they are; the Lean merge plan adds the parts up when something reads the table or they pass a size bound (#1329, #173). A weight sum that leaves 64 bits is raised at the later read that adds the parts up, not at the refresh that caused it. Polars and Spark share one implementation of the parts (`sverify._parts`). Four inserts of a quarter of the rows each into a filter view peak at 695 MB where they peaked at 947 MB over two million rows, and at 1369 MB where they peaked at 2314 MB over eight million; a refresh of a built state costs the change, 0.1 s for 100,000 rows at either size.

### Polars keeps a pipeline view's state in Parquet files it writes and scans

On Polars, an incremental view's state is a generation of Parquet files that Polars writes and scans lazily, where it was an Arrow table in the Python process (#1329, #173). Merging a change into the state runs the merge plan on Polars. The Polars translation takes `rows="multiset"` (as `to_sql` does), which lets an aggregate emit its groups in any order: the merge of a state peaks at 651 MB where it peaked at 1078 MB for two million rows.

### Spark keeps a pipeline view's state in Parquet parts it writes and reads

On Spark, an incremental view's state is a list of Parquet parts that Spark writes and reads, where it was an Arrow table in the Python process (#1329, #173). A refresh writes the change as a new part; the Lean merge plan adds the parts up when something reads the table or they pass a size bound. The driver's peak for four inserts into a filter view is 591 MB where it was 708 MB over two million rows, and 1289 MB where it was 1849 MB over eight million; a refresh takes about 2.9 times as long as before on a local session.

### The state location takes a URI, and Spark sizes its consolidation

`SVERIFY_STATE_LOCATION` names where Polars and Spark write an incremental view's state: a directory, or a URI that the driver and every executor read and write. Spark's consolidation of a state sets its shuffle partitions for the state's size: 8.4 s at eight million rows where Spark's default of 200 partitions took 9.9 s. The interim Arrow store (`sverify._arrow_state`) is gone.

### An engine plugin brings its state store: `ProfilePlugin.store`

`ProfilePlugin.store` makes the state store an engine keeps an incremental pipeline's state in. DuckDB keeps it in a DuckDB table, Polars and Spark in Arrow tables, as before. A plugin without one runs one-shot plans only, and refreshing a node on its engine raises an error that says so, as a dialect-only plugin like `sverify-snowflake` does. `ProfilePlugin` is outside the 1.x promise ([stability.md](docs/stability.md)), so a plugin written for 0.8.0 adds the field to keep refreshing on its engine ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189), [#1359](https://github.com/AlexanderNenninger/substrait-lean/pull/1359)).

### `sverify check query.sql --schema schemas.yaml` (#1362)

A bare `.sql` file is a `check` target: one query, the types of its tables from a
YAML or JSON file (`{table: {column: type}}`), and the verdict `verify` gives with
no contract. `--dialect` and `--semantics` take `sverify.sql`'s values and defaults.
The JSON, SARIF and GitHub outputs are those of a Python file.

### `sverify check` on a `.sql` file with an unterminated string exits 2 (#1362)

A tokenizer error of the SQL parser was a traceback; it is a usage error naming the parse failure.

### `ProfilePlugin.sql`: a dialect's SQL front-end (#1362)

A plugin can read a SQL dialect: `ProfilePlugin(sql=SQLFrontEnd(read, lift))`.
`sverify.sql(dialect=)` looks the dialect up among the installed plugins (an
unknown one names those installed), and DuckDB's own lift is registered the same way.
The dialect's semantics is the engine's name, accepted only where the plugin brings
the checker's profile. A report of SQL read by a front-end other than DuckDB's names
its package and version. `PLUGIN_API` is 4: engine packages need the same release.

### Spark's written plan has one model; Polars's and Spark's soundness theorems apply to an example

`Engine.polars_sound` and `Engine.spark_sound` are each applied to one example plan that meets `Engine.GuardFreeSide` ([#1441](https://github.com/AlexanderNenninger/substrait-lean/issues/1441)). Spark's written plan is modelled by `Profile.sparkWritten` alone: the hand-written `Spark.bin` is gone, and `date_add`'s wrap at 2³¹ days is a row of `Profile.spark` under `date_range` (spark-date-range). `Rel.spark_sound` keeps its name.

### `semantics="polars"` is reported as pending

The checker does not report under Polars's own profile yet, as for Spark
([#1288](https://github.com/AlexanderNenninger/substrait-lean/issues/1288)).
`verify(semantics="polars")` now gives the reference's report with a
`ProfilePendingWarning` (`report.semantics` says `"reference"`), and the plan
reaches Polars by the `translated` route, which computes the stated `FLOOR`.
The `native` route to Polars and the `recheck` route from a DuckDB report to
Polars are refused until the checker proves under `Profile.polars`
([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)).
Polars's observation rows now apply to Polars's tables.

### The checker's engines carry their soundness proofs

The list `substrait-check` is built over holds each engine's `Engine` value
with the proof that its run is sound (`EngineEntry`,
`engines/Sverify/Engines/Entry.lean`), so an entry whose theorem does not
state its engine's soundness no longer builds
([#1443](https://github.com/AlexanderNenninger/substrait-lean/issues/1443)).
`--realizability`'s `"theorem"` names that proof (`Engine.duckdb_sound`,
`Engine.polars_sound`, `Engine.spark_sound`), and a new `"side"` the side
condition it holds under (`Engine.NoRaiseSide`, `Engine.GuardFreeSide`). An engine package from outside
builds its checker over `builtinEntries ++ [its entry]`, copying
`SubstraitCheckExamples/DummyEngine.lean`; `EngineProfile.translationTheorem`
and `asReference` are gone, and a request under such an engine's profile is
pending like a built-in one's.

### The as-of join's cap holds for every table, counted at the run

`sv.asof_join`'s `max_pairs` used to count the pairs only when both tables were Arrow tables held by a `sverify.connect()` connection; a join over Parquet files or an engine's own tables ran with no bound. The checker now reads each as-of join off the plan and writes the count of its pairs as a plan of its own, which `Report.run` evaluates on the engine before the join, whatever the tables are. The refusal above `max_pairs`, with the same exits, now comes from the run instead of from `asof_join` ([#1447](https://github.com/AlexanderNenninger/substrait-lean/issues/1447)).

### `asof_join` refuses a join that would compare more than 10⁸ pairs of rows

`sv.asof_join` is a range join, so the pairs of rows it compares (each left
row with every right row of its `by` group) are quadratic in the rows
([#1447](https://github.com/AlexanderNenninger/substrait-lean/issues/1447)).
Where both tables are held by a `sverify.connect()` connection, it now counts
them and raises `UnsupportedError` above `max_pairs` (default 10⁸, which keeps
DuckDB's join under about 7 seconds), naming the exits: `by` columns, fewer
rows, or a larger cap (`max_pairs=None` for none).

### DuckDB runs `asof_join` as its ASOF JOIN

On DuckDB, `sverify.asof_join` without a `tolerance`, over integer, date, timestamp or string columns, runs as `ASOF [LEFT] JOIN` ([#1447](https://github.com/AlexanderNenninger/substrait-lean/issues/1447), [`duckdb-asof-join`](engines/duckdb/facts/duckdb-asof-join.json)). It compares no pairs of rows, so the `max_pairs` cap does not apply there; the other engines and a join with a `tolerance` keep the range join and the cap. At a tie on the right DuckDB's pick may differ from the range join's: both are allowed, and the report already says `deterministic` is false for such a plan.

### Maintained double aggregates keep their exact state in the engine

A maintained `SUM`, `AVG`, `VAR`, `STDDEV`, `COVAR` or `CORR` of doubles keeps
its exact moments as integer limbs, rows of the group state that the engine
adds up with its own `SUM` (#1447). A batch no longer brings each changed row
to the driver: Python reads the limbs of the touched groups and rounds them
once, so the results are unchanged (D25, D30), on DuckDB, Polars and Spark. The state takes about half the
bytes of the decimal strings it replaces. A group with `2⁴¹` values or more,
past what the limbs hold, raises.

### Exact double aggregates fold in Arrow, whatever the values

A maintained `SUM`, `AVG`, `VAR`, `STDDEV`, `COVAR` or `CORR` of doubles used to add rows with a NaN, an infinity or a weight of 256 or more to its exact state one at a time in Python. Arrow now sums them per group like every other row, so a batch full of NaNs or of rows repeated many times folds about twice as fast, and the result is the same exact state ([#1447](https://github.com/AlexanderNenninger/substrait-lean/issues/1447)).

### The user pages of the docs name no Lean theorems

The how-to and explanation pages say what a guarantee is in plain words and link the reference pages for the Lean names, and a test checks it, along with every link and anchor of `docs/` and the old place of the engine facts ([#1448](https://github.com/AlexanderNenninger/substrait-lean/issues/1448)).

### The SQL writers print raw doubles

The DuckDB and Spark writers no longer add `+ 0.0` to float reads, scalar results and aggregates. The written plan gave `atan2((0.0 * -1.0) + 0.0, -1.0) = π` where the reference gives `-π`, and `1.0 / (x * -1.0)` gave `inf` for `-inf` under `semantics="duckdb"` (#1461). `round` and `ceil` print the proved template on DuckDB, and a stored `-0.0` now reaches the model: the plan's literal is the text `-0.0`, which the parser reads. DuckDB's own comparisons, groups, joins, window partitions and sort keys already read the zeros as one.

### The DuckDB and Spark writers print a zero class's canonical value for MIN, MAX and keys

Where the engine's pick among equal zeros depends on row order or partitioning (`MIN`, `MAX`, `QUANTILE_CONT` and `MEDIAN` of doubles on DuckDB and Spark, and a double group key or `DISTINCT` row on DuckDB), the written plan adds `+ 0.0`, so a rerun gives the same sign and the plan stays inside the reference's allowed values (D31). `sverify.testing.canonical` reads `-0.0` as `0.0` and says so in its docstring (#1461).

### A variance, covariance or correlation of an infinity reads nan_creation

A variance, standard deviation, covariance or correlation of a `+∞` or `-∞` is a NaN made by the aggregate, so `nan_creation` governs it (as for a double `SUM` or `AVG`). Under `semantics="polars"`, `"spark"` and `"duckdb"` (whose profiles all have `nan_creation = NAN`) the checker no longer bounds such a result by the statistics' properties, and any value is allowed there. The reference still raises, so a verified plan under the reference is unchanged. The evidence of a DuckDB route that reads `agg.var` or `agg.stat` goes from proved to tested for `nan_creation` ([#241](https://github.com/AlexanderNenninger/substrait-lean/issues/241) tracks the proof), and verdicts and Substrait manifests list the read ([#1469](https://github.com/AlexanderNenninger/substrait-lean/pull/1469)).

### QUANTILE_CONT of infinities reads nan_creation; Polars and Spark interpolate as LINEAR_DIFF

`quantile_cont` and `median` between a `-∞` and a `+∞` neighbour are a NaN made by the aggregate: `nan_creation` governs them, and the reference raises. Polars and Spark compute `lo + (hi − lo)·w`, which is NaN with a `-∞` lower neighbour and any greater upper one; their `quantile_interp` behaviour is now `LINEAR_DIFF` (between the neighbours, or NaN), and their quantile rows are refused under the reference route ([#1475](https://github.com/AlexanderNenninger/substrait-lean/pull/1475)).

### A Polars or Spark run no longer runs the plan on DuckDB first

A report with assumed issues (an integer `SUM` that must fit, an operation on finite doubles that must not give `±∞`) ran its plan on DuckDB before the target engine to check them, which doubled the run and made DuckDB's errors everyone's. The Polars and Spark translations check them as they run, so `Report.run` runs the plan on the target engine only, and a batch that breaks one is refused with the same `PreconditionError` (#1484).

### Reports name the black-box laws a proof trusts

`Report.black_boxes` maps each black box a plan calls (DuckDB's `entropy`,
`base64`, …) to the laws its row declares, as `sverify.black_box.Law` tuples,
and `str(report)` prints one line for each, such as `trusts: black box entropy
keeps its declared laws (non_null, at_least 0)`. The report's JSON keeps them
under `black_boxes`. If an engine's function ever breaks a declared law, the
checker refuses to print the rows instead of showing the row's sample value
([#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484)).

### The report says which build of the checker proved it

A checker built without `check_generated` (a plain `lake build`, an editable
install, `SVERIFY_CHECKER`, a borrowed binary) holds its generated lift and
lowering proofs as `sorry`. The report's JSON gains `checker.generated_proofs`
(`true`, `false`, or `null` where the checker does not say), and `str(report)`
starts with "proved by a checker whose generated proofs are unchecked" for such
a build. The proof cache already separates the two builds by the checker's hash (#1484, [trusted base](docs/trusted-base.md)).

### `Report.deterministic` holds up to the member of a class of doubles (D48)

`Report.deterministic` is now true when every result the reference allows is
the same up to row order and up to which member of a class of doubles it
keeps: `-0.0` or `0.0`, and which NaN (`check_class_determined_sound`). A
`GROUP BY` or `DISTINCT` key over doubles, `MIN`, `MAX` and `QUANTILE_DISC`
no longer make it false, so a refresh or a sink epoch of `SELECT region,
MAX(price) … GROUP BY region` over a double `price` runs under the default
`reproducible=`. An expression that reads a picked double and can tell `-0.0`
from `0.0`, such as `atan2`, still makes it false, and the report names the
expression.

A rerun requirement that reads the members of a class, `sv.equivalent()`
with exact doubles and exact zeros, still refuses each such pick. The
refusal names the pick and the two ways out: an observation that reads one
zero and one NaN (`floats="plan"`, the sinks' default, or
`zeros="canon"`), or a plan without the pick.

`sv.equivalent(floats="plan")` now compares `-0.0` and `0.0` as equal also
where the plan has no bound on its doubles.

### Decimal `+` and `-` raise where DuckDB's operand cast does

DuckDB casts each operand of a decimal `+` or `-` to the result type and raises there, also where the exact sum fits (`DECIMAL(38,0) + DECIMAL(38,10)` at `10^28` against `-0.0000000001`). The reference returned the value. It now checks an operand that can exceed 38 digits at the result's scale and raises, and the inferred precondition is `|a| < 10^(38 - s)` (D56, [#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484), `duckdb-decimal-addsub-operand-cast`).

### `--delta` names the operator that has no delta rule

`substrait-check --delta` and `NotIncrementalError` said "not incrementally maintainable (left join, fetch or window)" for every plan without a delta rule, a global aggregate and `COUNT(DISTINCT …)` included. The message now lists each blocking operator with the tables under it: `no delta rule for aggregate over orders; left join over orders, customers`.

### `Report.deterministic` is a theorem

`Report.deterministic` is now `Rel.detPlan`, and when it is true every result
the reference allows is the checker's up to row order
(`check_deterministic_sound`, #1484 finding 9). Before, it checked only ties
in windows, ordered aggregates and `LIMIT`s. It now turns false in four more
places, and `tie_places` names each one:

- `MIN` or `MAX` over doubles, a group key over doubles, or a `DISTINCT` over
  doubles, where the reference keeps any member of a class (`0.0` and
  `-0.0`, the NaNs; D31);
- `QUANTILE_CONT` of doubles (the median), which may be any double between
  the two neighbours;
- an aggregate the checker has not proved a function of its values, such as
  `AVG` of integers;
- an ordered aggregate whose argument is a sort column holding doubles, since
  `0.0` and `-0.0` tie.

A `LIMIT` over an `ORDER BY` on a key stays deterministic, and so does an
ordered aggregate (`first`, `last`, `group_concat`, `mode`, `arg_min`) whose
group and order hold a key. A `LIMIT` over a clustered sort is no longer
deterministic, because the reference leaves the order of the groups open.
Over 2,394 recorded requests, 50 turn false: 22 for `MIN`/`MAX` over doubles,
17 for an `AVG` of integers, 6 for the median of doubles, 4 for a group key
over doubles and 1 for an ordered `ARRAY_AGG` over ties. None turns true. A
rerun requirement (`reproducible=`) refuses these plans. D48 then counts the
first bullet's picks as determined again, up to the member of a class
(`1484-d48-class-level.md`).

### Postconditions are proved over the transformation itself

`substrait-check --contract` builds each postcondition's plan from the
request's transformation and refuses a postcondition plan that selects from
anything else, so `check_proved_sound` speaks of the transformation the report
is about (#1484, finding 2).

This fixes a soundness hole in `Report.from_substrait`. An exported plan carries
the shims the export applied, and the postconditions' plans in the export do
not. The recheck proved the postconditions of the plan without the shims and
reported them for the exported plan. It now proves each condition over the
exported plan. An export whose condition reads another relation is refused
with an error that says to verify and export again.

An Ibis condition over a transformation that ends in a join's `select` is no
longer merged into that select by Ibis.

### The oracle of `allows_rows` has a theorem for most plans

`Rel.evalChoices_allowed` (`analysis/Sverify/Analysis/ChoicesSound.lean`) proves that a result `allows_rows` accepts is one the reference allows (`Rel.OrderAllowed`), for plans without an ordered aggregate (`FIRST`, `LAST`, `STRING_AGG`, `collect`, `MODE`). The other plans stay tested; the next changes prove them one at a time (#1484).

### The oracle of `allows_rows` groups by canonical key

`sverify.testing.lean_choices`, the oracle of `allows_rows`, grouped and deduplicated by exact equality where the reference does it up to canonical codes (D31): keys `-0.0` and `0.0`, or two NaN payloads, gave two groups, each over the whole class's rows, so an engine's single row was rejected. It groups with `distinctRows`, as `Rel.eval` does.

### The first line of a report says "proved with checks"

`str(report)` and the markdown note started with `proved` for a plan proved under assumptions that a run checks on the data (`Report.assumed`), which hid what the verdict says. The line now reads `proved with checks: 2 assumptions`. The JSON `summary` carries the same text ([#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484)).

### An integer literal next to a TINYINT or SMALLINT column has the column's type

DuckDB types an integer literal next to a narrower integer operand as that operand when the value fits, so `tiny_col + 100` is a `TINYINT` and raises past 127. The SQL lift widened the column to `INTEGER` and would not have raised. It now follows DuckDB in arithmetic, `COALESCE`, `CASE`, `GREATEST`, `LEAST` and `NULLIF`; a literal that does not fit widens the column as before (`tiny_col + 200` is an `INTEGER`). Any other query that puts an integer literal next to a `TINYINT` or `SMALLINT` (a list literal, a `lag` default) is refused, naming `CAST(100 AS INTEGER)` ([#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484), `duckdb-coerce-int-literal-width`).

### An integer `AVG` is a function of its values

The checker now proves that an `AVG` with an integer result (the truncated
mean) depends on its group's values only, as `SUM` and `COUNT` do
(`AggFn.orderFree`). Two results change:

- `report.deterministic` is true again for a plan whose only open place was
  an integer `AVG` ("not proved a function of its values").
- `run_sharded` runs an integer `AVG` grouped by the split key on each shard
  as it is (`linear`), where it split the mean into a `SUM` and a `COUNT`
  (`two_phase`) before.

### No runtime error on every order of the ties

The proof that a plan with no reported issue raises no runtime error now
covers every order of the ties the reference allows (`Rel.mayIssues_sound_all`,
#1484). Before, it covered one order, the reference evaluator's. An engine that
breaks a window's ties another way, as the routes for windows on Spark and
Snowflake allow, is covered too. The issues sverify reports are unchanged.

### Errors in a condition on one side of a join

The proof that a plan with no reported issue raises no runtime error now
covers a condition that an engine evaluates on one side of a join before any
pair exists, even when the other side is empty. DuckDB pushes a filter on one
side into that side, and a hash join computes a key such as `10 // a.x` on
every row of its side (#1484). Before, this case was outside the proof. The
issues sverify reports are unchanged.

### A raising constant in a lambda's body is reported under a guard too

`Expr.constIssues` read a lambda's list and not its body, so `ifelse(id > 5, xs.map(e -> e + 1 // 0), NULL)` under a precondition that no row passes was proved, where D21 counts every constant subexpression that raises as raising for the whole plan. The body is read now ([#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484), K5 of ruling 100). No engine run raised: DuckDB has no SQL form for lambdas yet and Polars returned NULLs.

### Closed plans without doubles are proved near-safe on DuckDB, Polars and Spark

Sverify proves that a plan in which no double occurs gives, on an engine's table, only results the reference allows, where the table with the reference's choices at the options only doubles read transfers (`Rel.transfer_of_noDouble`, [#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484)). The run plan's `near` gate now rests on that theorem: under `floats_plan` or an `approx` postcondition, a rewrite runs only where neither plan has a double or an open measure and both transfer at DuckDB, Polars and Spark. Plans the theorem does not cover keep their `run_gate` of `near`: a plan with an integer `MIN` or `MAX` (they read `list_null_order`, where every engine's table differs from the reference) or an integer `AVG` (`avg_int_result`), and a plan with an integer `BIT_AND`, `BIT_OR`, `BIT_XOR` or `QUANTILE_DISC`, which is not closed.

### `NULLIF` in SQL has the type of its first argument

DuckDB's `NULLIF(a, b)` compares in the common type of `a` and `b` and returns `a` itself. The lift typed the result as the common type, so `NULLIF(int_column, double_column)` was a double and an addition on it did not raise where DuckDB's integer addition does. Where the two types differ, the lift now writes `CASE WHEN a = b THEN NULL ELSE a END`; `NULLIF` of two values of one type is unchanged ([#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484), `duckdb-nullif-type`).

### A function option takes its first supported preference

A plan may list several preferences for a function option, and Substrait applies
the first one the engine supports. The parser accepted an option when any
preference was supported but modelled the first listed one, so
`on_division_by_zero: ["IEEE", "NULL"]` on an integer `divide` was read as `IEEE`.
`checkOptions` now keeps the supported preferences and the parse reads the first
of them (#1484, R1).

### `Report.output` types decimal aggregates as the run returns them

`Report.output` took its types from Ibis, so a decimal `AVG` said `decimal(10, 2)` where the run returns `decimal(14, 6)`, and a decimal `SUM` said `decimal(38, 2)` where it returns `decimal(20, 2)`. The checker now reports each output column's type (`outputKinds`, from `Write.relKinds`), and `Report.output` states a decimal column's precision and scale as the checker types it, which the ODCS and OpenLineage exports and sverify-dbt's contract check read. A checker without the field leaves Ibis's types as they were ([#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484)).

### `Report.output` states the run's integer widths

`report.output` now types an integer column as the run returns it: `int64` for a computed integer (`i8 + i8`, `abs(i8)`, `-i16`, `year(ts)`, `length(s)`), the declared width for a column passed through, and `timestamp(6)` for a timestamp. It said Ibis's widths before (`int8` for `i8 + i8`), which the run did not return. Code that read a computed column's width from `report.output` sees `int64`. A Polars run casts a passed-through narrow column back to its declared width (it returned `int64`). The contract report's `outputKinds` carries an integer's `bits`. An explicit cast gives today's width in both; writing the width it names is #1772.

### `requires` are checked on the run's own engine

`Report.run` checks a report's preconditions on the engine it runs on, as one checker-written plan per table that counts every condition, where it ran an Ibis count per condition on the table's backend. A result that is not TRUE is a violation, a condition plan that raises is a violation (`PreconditionError`, "raised on"), and a condition the engine's writer refuses refuses the run, with no fallback to Ibis. A DuckDB run by the reference's translation no longer runs the plan once beforehand for its assumed `SUM`s and operations on finite doubles: the translation checks them as it runs ([#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484), S3 and S4). A report read back with `Report.from_substrait` now checks the preconditions the export carries before it runs, as the report `sv.verify` returned did (a row condition by its own plan, `unique` and the other table conditions as before), where it ran on data that broke them and, on Polars, without the plan's guards; a run refuses a report that holds a precondition it has no check for ([#1513](https://github.com/AlexanderNenninger/substrait-lean/issues/1513)).

### Spark refuses a decimal comparison it would round

Spark compares decimals of different scales in a common type and, where that type passes 38 digits, rounds the operand of the higher scale: `CAST(2 AS DECIMAL(38,0)) = CAST(1.5 AS DECIMAL(38,10))` is true on Spark. The Spark writer now refuses such a comparison, and `GREATEST` or `LEAST` of such a pair (the common type has `max(p₁ - s₁, p₂ - s₂) + max(s₁, s₂)` digits), naming the two types; a pair that fits 38 digits is written as before and is exact (`spark-decimal-compare-scale`, #1484).

### `to_sql` writes the rows the engine's runner writes

`to_sql`'s default for `rows` follows the engine (`"multiset"` for Spark and Snowflake, `"sequence"` for DuckDB), so a bare `to_sql(plan, "spark")` writes FETCH and windows over a named table with ties open, as a run on Spark sends them, where it refused them. `rows="sequence"` stays refused there; the message names `rows="multiset"` and the report's `deterministic` as the ways on. `Node.to_sql("spark")` of a node without a report writes what its refresh runs.

### A column no query mentions blocks nothing

A struct column the DuckDB writer has no SQL form for, a `map` column of a Delta table, a zoned timestamp or an unsigned integer failed every plan over their table, also where no query read them (`SELECT d, e, d + e FROM t`, `DeltaSource(...).pipe(agg)`). Such a column is left out of the plan when the transformation and the conditions never mention it. A query that reads it still refuses, now naming the column: `column 'm' of 'orders': type map<…> is not supported`.

### `sverify check` proves a decorated transform on its declared schemas

`@sv.transform(schemas={"orders": {"id": "int64", "amount": "int64"}})` gives a
transform its input schemas. `sverify check pipeline.py` then proves the contract
of a transform the file never applies, as `paid.verify(orders=...)` does, with no
driver script. Without `schemas` the file's `unchecked` message names the new
exit (#1485, item 10).

### Dagster and Airflow examples

`templates/orchestrators/` has a Dagster asset check and an Airflow DAG that prove a
transform's contract before they run it, tested with dagster 1.13.30 and
apache-airflow 3.4.0 ([compatibility](templates/pipelines/docs/compatibility.md), #787).

### Ranges of double arithmetic are the exact result's, rounded at the ends

The checker bounded a double `+`, `-` or `*` by the exact result widened by an error term, so `a / 8` of `a` in `[0, 8]` came out as `< 1.0000000000000009` and `amount * 3 + 1` of `amount` in `[0, 1e300)` as `≥ 0.0`. The ends are now rounded as the operation rounds them (rounding is monotone), and so is a quotient by one divisor: `a / 8`, `a * 0.125` and `(x + y) / 2` are in `[0, 1]`, `x + y` in `[0, 2]`, and `amount * 3 + 1 > 0` is proved ([#1485](https://github.com/AlexanderNenninger/substrait-lean/issues/1485), items 7 and 26). A bound with one end only (`amount >= 0`) still gives `any double`.

### Every module imports without DuckDB, and `verify` runs without it

Importing any `sverify` or `sverify_duckdb` module no longer imports `duckdb`, and `sv.verify` proves a plan, from Ibis or from SQL, in an environment that has none. What runs on DuckDB (`sv.connect("duckdb")`, table reads and sinks) raises `ImportError: this needs DuckDB: pip install 'sverify[duckdb]'`. The DuckDB engine counts as installed for running plans only where `duckdb` is. DuckDB is still a dependency of `sverify`; moving it to an extra follows (#1485, 16).

### DuckDB is an extra: `pip install 'sverify[duckdb]'`

`pip install sverify` now installs no engine and no `duckdb`: `sv.verify`, the SQL dialects and `report.to_sql` work, and everything that runs plans or holds tables raises `ImportError: this needs DuckDB: pip install 'sverify[duckdb]'` or names the extra of the engine. That makes sverify installable beside `soda-core-duckdb` (`duckdb<1.1`). Add the extra where you relied on the implicit DuckDB: `sverify[duckdb]`, or `sverify[all]`, which now includes it. `sverify-dbt` brings DuckDB itself (#1485, 16; #1288).

### First-hour stumbles

`sverify check revenue.sql` exits 2 and says to check SQL through `sv.sql` in a `.py` file or a dbt project, in place of "not a Python file" and exit 6. The internal `DOUBLE(…)` cast no longer shows around an aggregate, and the check's output no longer ends with a bare status line after the node's own verdict. A counterexample prints a date or timestamp in the output as a date or timestamp, as the input does, which also fixes sverify-dbt's `order_date = 0`. The `SUM` hint leads with the run-time check, and its example row cap is one anyone would write (#1485).

### sverify-dbt keeps an incremental model's tests out of `sverify_proved`

`sverify check` proved an incremental model's tests from its full-refresh SQL and listed them under "dbt build may skip them", so `dbt build --exclude selector:sverify_proved` dropped them even where an incremental run (the `append` strategy, or `merge` on another key) could break them (#1485). The tests of an incremental model are now skippable only for the `merge` or `delete+insert` strategy on a `unique_key` that a proved `unique` test names. Otherwise they are reported as proved for the full refresh and `dbt build` keeps running them. Proving the incremental branch is a follow-up.

### `lean_values` raises on join conditions too

`sverify.testing.lean_values` raises `LeanRaised` where the reference raises in a join or semi-join condition, on the pairs the checker's hash join tests (`substrait-check --raises`), so a raise on a pair without matching join keys can be missed; every error it raises is the reference's. A window's aggregates are not looked into: a frame may leave a row out.

### `lean_values` raises on a window's aggregates too

`sverify.testing.lean_values` raises `LeanRaised` where the reference raises in the argument or filter of a window's aggregate, on the frame of each row (`substrait-check --raises`): a row that no frame holds raises nothing.

### A message names a computed column the output drops

An overflow over a column that an earlier step computes and the output never keeps
reads `amount * 2 * 3 + 1`, where it printed Lean's `(($1 * 3) + 1)`.

### Clearer messages: names, vacuous requires, suggestions

An overflow after an aggregate names the measure (`sum(amount) * 2 + 1`) where it
printed Lean's `($1 * 2) + 1`. `sverify check --diff` prints the report's other
fixes (a row cap for an unbounded `SUM`) where no precondition helps, in place of
"No preconditions to add". A report hints at `requires` that no row can meet, such
as `amount > 5` with `amount < 3`, which made every `ensures` hold with nothing to
check. A misspelt column in `requires` or in SQL suggests the closest column.

### A clear message where no wheel exists

PyPI carries wheels for Linux (x86_64, aarch64) and macOS on Apple silicon. On Windows and Intel macOS, `pip install sverify` used to fall back to the sdist, which needs elan and a full `lake build`. The sdist's build now stops at once and names the platforms with a wheel, WSL2 or a container as the way out, and `SVERIFY_BUILD_FROM_SOURCE=1` for building from source (#1485).

### One-sided bounds through a double difference and quotient

A double difference keeps its lower end where the minuend has a finite lower end and the subtrahend a finite range (`amount - 1` with `amount >= 0` is "a double ≥ -1.0"), and a quotient of a non-negative dividend by a divisor with a positive lower end is at least `0.0`, each with one end only (#1485 items 7 and 26). The upper end of such a quotient is not kept: the divisor may be NaN, which is above every bound.

### An overlapping refresh that loses the commit race reports "already committed"

When two refreshes of one sink overlap and the other commits the same state first, the slower refresh returns that state as already committed instead of raising `ConcurrentWriteError`. If the sink holds a different state, the error stays (#1485).

### A sink records the engine, its version, the release and the profile that wrote a state

A sink's contract record gains optional fields `engine`, `engine_version`, `sverify`, `profile` and, for an engine that comes from another package than sverify, `package` (`name==version`). Records written before them read as unknown and resume as before; the record's format stays 2. A restarted job that finds another engine or engine version than the record names says so in `started` (`engine duckdb → polars`): a view that is recomputed and diffed resumes, a view maintained from its state resumes where its report proves the plan determined (every engine then holds the same rows), and is recomputed once where the plan leaves a value open. A changed release alone is in `StageRefresh.record_changes` only. The profile a plan was verified under (`semantics=`) is a component of the plan's digest, left out for the reference, so a sink written under another profile recomputes once, and the refresh names both profiles; digests of reference plans are unchanged ([#1485](https://github.com/AlexanderNenninger/substrait-lean/issues/1485)).

### A refresh logs each node and each commit

A refresh writes one INFO line per node and one per commit to the `sverify` logger, in the words of `Refresh.summary()` ("paid: committed merge v5: +2 −0", or "already committed" where an overlapping refresh had committed the same state), so an orchestrator's task log shows what ran without printing the summary (#1485 item 25).

### Reports name the transform's parameter

When the result of one contracted transformation feeds another, the downstream report says `requires orders: …`, the name in its own `requires`, in place of the name of the upstream transformation that feeds it (`requires latest: …`). The same holds for the "needs" text (#1485).

### `print(report)` is the contract in plain words

`str(report)` now says what holds, what each run checks on the data and what is not proved, in the words `sverify check` uses (table names are the transform's parameters). The full text, with the semantics, the evidence for each engine, the routes and the observation, is `report.details()`, which `sverify check --full` prints (#1485).

### The sdist carries the file the Lean statements read

The sdist now includes `tests/contracts/int_division.json`, which `SubstraitLean/Statements.lean` reads, so the wheel built from it compiles again. `tests/test_sdist_inputs.py` checks that every `include_str` path in the Lean sources is in the sdist (#1485).

### `DeltaSource(uri, schema=...)` and `IcebergSource(catalog, id, schema=...)`

With a declared schema, building a node and `sverify check` prove a transform without opening the table: no lake credentials or network on a pull request, and no failure for a table that does not exist yet. Every refresh reads the table's schema and raises `SchemaError` naming the differences when it is not the declared one (#1485, 18).

### SQLGlot from 30.8, beside SQLMesh

`sverify` requires `sqlglot>=30.8.0,<30.18` in place of `~=30.17.0`. The lift's tests pass on every release from 30.8, the one SQLMesh 0.235 and later pin, so `pip install sverify sqlmesh` resolves to a current SQLMesh in place of falling back to 0.4.1 (#1485).

### The plan digest a sink records is stable across releases

A sink's contract records a digest of the plan that wrote it, and a refresh resumes from the sink only when the plan's digest is the same. The digest used to be the sha256 of the plan's text, which lists every function the writer knows, so each release that added or dropped a function changed it and the first refresh after an upgrade rewrote every sink in full. The digest is now the sha256 of the plan with that list left out and each function reference replaced by the function's name: the same plan gives the same digest in 0.7.0 and 0.8.0, which the critique's run showed ([#1485](https://github.com/AlexanderNenninger/substrait-lean/issues/1485), finding 24). This release recomputes sinks once, as it changes the digest; the ODCS and OpenLineage exports record the new digest too. A release that changes the canonical form, or what a plan means, says so in its changelog. The digest also hashes in a record of the changes that make an unchanged plan compute another result (`MEANING_CHANGES`): a decision that changes a value of the reference or narrows what it allows, and the fix of a wrong result of a lowering. A sink written before one is recomputed, and the refresh says which change did it; a decision that only opens a choice leaves the digest alone, and each decision after D49 says which it is (`Recomputes sinks: yes` or `no`).

### `verify` holds schemas, not a DuckDB connection

`sv.verify` builds its plans over unbound Ibis tables and the lift reads the input schemas directly, so a verification no longer starts a DuckDB database and uses about 30 % less memory. Results are unchanged. This is the first step of moving DuckDB to an extra (#1485, 16).

### Polars raises where its variance of finite values is NaN

Over finite values, Polars's ungrouped `var` can come back NaN where the reference gives a value (`[1e308] * 100000` gives NaN against the reference's 0.0). The written plan now raises `VarianceNaN`, with or without guards, and the message of the infinity raise names the algorithm's intermediate steps too ([#1486](https://github.com/AlexanderNenninger/substrait-lean/issues/1486)).

### The statistical aggregates' model says what it knows outside `Stat.fits`

`StatProps` (the model of Welford's and the generic algorithms) asked for the reference's own value for finite values past 2³² rows or 2³⁹⁸ in magnitude, which DuckDB and Polars do not give (`var_pop([1e150, 3e150])` differs in the last digits). Those inputs are now open, any double; NaN and infinities keep the reference's value. No verdict changes: the route already reports such columns unproved ([#1486](https://github.com/AlexanderNenninger/substrait-lean/issues/1486), D30).

### A `VALUES` row that raises or misses its type is refused

The parser evaluated each row of a `virtualTable` when it read the plan, so an overflow or a division by zero in a computed row never reached the safety analysis, and it never compared a cell or an integer literal with its declared type, so `--write` could emit a plan no consumer accepts. A field that is not a literal is now refused (as the SQL lift refuses `VALUES` of computed values), a cell must fit its column's type (`Parse.literalFits`), and an `i8`, `i16`, `i32` or `i64` literal must fit its width ([#1491](https://github.com/AlexanderNenninger/substrait-lean/issues/1491)).

`right(s, n)` for `n = -2**63` no longer lifts to an `i64` literal one past the type's range (`1 - n`); the offset is capped at the largest one DuckDB's `substring` takes, so the query stays checkable, which the width check on literals would otherwise have turned into a refusal.

### Strings and booleans can be ordered on DuckDB and Polars

A verified plan that compares strings or booleans with `<`, `BETWEEN`, `GREATEST` or `LEAST` now runs on
DuckDB and Polars, in the model's order: code point for strings, `FALSE < TRUE` for booleans. Before, `verify`
proved such a plan and both translators refused to run it (#1492).

### Decimal comparisons across scales and wide decimal averages no longer overflow DuckDB

A comparison of decimals of different scales was proved but raised on DuckDB, which casts both sides to one `DECIMAL(38, s)` and fails where a value does not fit (#1498). The DuckDB writer now compares the unscaled integers, with the scale gap's floor and remainder, so no cast can fail. A decimal `AVG` over `DECIMAL(p, s)` with `p` above 34 is refused (its `DECIMAL(p + 4, s + 4)` result does not fit 38 digits and the model had no overflow check for it), and the writer's quotient for the rest no longer multiplies the sum past 38 digits (#1497).

### A decimal quotient is checked against its declared type

`sverify_decimal_div` reads as an unchecked decimal only where its declared `DECIMAL(p, s)` follows from its operands: the numerator's precision plus the upscale, or, for the `SUM` and `COUNT` of one argument, the summed argument's precision plus the upscale. Elsewhere it reads as the checked decimal, so `verify` reports an overflow where the quotient can have more digits ([#1497](https://github.com/AlexanderNenninger/substrait-lean/issues/1497)).

### The trust in an incremental view's maintenance plans is stated

The checker parses and writes the plans that maintain an incremental view (state, contributions, merge, finish) and does not contract-check them, so a view's report is its batch query's and a refresh can raise where the report lists no issue; it then applies nothing. `docs/trusted-base.md` and the `_linear.py` docstring say so, and a test keeps a decimal `AVG` at `DECIMAL(34, 2)` with values of ±(10^34 − 1)·10^-2 equal to the batch `AVG` on DuckDB and Polars ([#1497](https://github.com/AlexanderNenninger/substrait-lean/issues/1497)).

### The refusal of a wide decimal `AVG` names the way through

`AVG` of a decimal over 34 digits stays refused, since its `DECIMAL(p + 4, s + 4)` result must fit 38 digits ([#1497](https://github.com/AlexanderNenninger/substrait-lean/issues/1497)). The message now says to cast the argument to `DECIMAL(34, s)` or narrower first, which verifies (the cast's overflow becomes an inferred bound) and runs to the exact mean, and `docs/reference-semantics.md` states both limits, precision and scale.

### `replace` with an empty pattern returns the string unchanged

The model's `replace` put the replacement around every character, as Polars
does, and DuckDB returns the string unchanged, so a plan verified with an empty
constant pattern ran on Polars with another answer than the SQL gave on DuckDB.
The reference now gives DuckDB's value: `replace(s, '', r)` is `s`, and NULL for
a NULL `r`. Both frontends accept the empty pattern, and the SQL writers and the
Polars engine fold it to `s`, so every route gives the same answer
([#1508](https://github.com/AlexanderNenninger/substrait-lean/issues/1508)).

### SQL `NTILE(k)` is proved

The SQL lift wrote `NTILE` as arithmetic over `ROW_NUMBER` and `COUNT`, whose
product was reported as a possible overflow that no precondition could rule
out, so no SQL plan with `NTILE` was proved. It now writes the model's `ntile`
window function, the SQL standard's buckets, as the Ibis producer does
([#1509](https://github.com/AlexanderNenninger/substrait-lean/issues/1509)).

### The state store matches double keys as `GROUP BY` does

An incremental refresh of a view grouped by, or `DISTINCT` over, a double column crashed with `ArrowInvalid: Cannot yet unify dictionaries with nulls` when a NaN key and a NULL key met, and kept `0.0` and `-0.0` apart, so a refresh after an append of `-0.0` gave a count of 1 where a recompute gives 2 (#1511). The store now encodes the combined key column once, with one zero and one NaN on its copy of the key (the stored values stay raw, D31), and NULL as its own key.

Sharded evaluation's split-key and `unique` checks compare doubles the same way (#1519): `0.0` on one shard and `-0.0` on another is now a split key `check_keys` refuses, where the sharded result had two groups for one.

### `QUANTILE_DISC` of doubles may return any zero or NaN of its class (D45)

The reference now treats `QUANTILE_DISC` as it treats `MIN` and `MAX` (D31).
Where the selected value is a zero or a NaN, any member of its class in the
group, or the class's canonical value, is allowed (`AggFn.Picks`). DuckDB
returns `-0.0` or `+0.0` by row order and thread count, and both are now
results the reference allows. No verdict changes.

### A window's `MIN`, `MAX` and `QUANTILE_DISC` of doubles may return any zero or NaN of its class (D45)

D45 now covers windows. Over a frame, `MIN`, `MAX` and `QUANTILE_DISC` allow
any member of the selected value's class among the frame's values, or the
class's canonical value, as they do in a group. DuckDB's windowed `MIN` and
`MAX` return either zero by row order (`duckdb-minmax-zero-sign`), and both
are now results the reference allows.

One verdict changes: a plan with a windowed `MIN`, `MAX` or `QUANTILE_DISC`
over an argument that may be a double loses its determinism certificate
(`report.deterministic` is false), and the report names the window function
("keeps any member of a class of doubles"). Over arguments without doubles
nothing changes.

### `asof_join` keeps every left row

`sv.asof_join` dropped all but one of the left rows that share their `by` and
`on` values (and the rows with a NULL `on`), and the plan was proved. The
ranking is now per left row, numbered first, so each row keeps its match and
the output has one row per left row. `unique(by, on)` of the output is no
longer proved: it was true only because rows were dropped. The `key=` parameter,
which named the columns that identified left rows, is gone
([#1517](https://github.com/AlexanderNenninger/substrait-lean/issues/1517)).

### Polars and Spark quantiles: LINEAR_DIFF reads the engine's double position

Polars and Spark compute the quantile position `(n − 1)·q` in doubles, so at some positions that are whole in exact arithmetic they interpolate toward the next value. Their `quantile_interp` behaviour `LINEAR_DIFF` now takes the neighbours of that double position, so it states what the two engines compute. The reference stays at the exact position ([#1527](https://github.com/AlexanderNenninger/substrait-lean/pull/1527)).

### `run` and incremental views count the NULLs of a table the engine reads where it is

The check of `Report.run` and of an incremental view's first load counted a NULL in a non-null column only on an Arrow table. A `Resident` table or a `Scan` of files now gets the same count, on the engine, beside the range check of its integer columns: a NULL in a column the plan reads as non-null is refused, naming the column ([#1540](https://github.com/AlexanderNenninger/substrait-lean/issues/1540)).

### `Report.run` checks the data against the schema the plan was verified for

`Report.run` compares each table it reads with the plan's `baseSchema` and refuses a mismatch before an engine reads a row, on every engine, naming the table and the column: a missing column, a type the reader would change (a double in a `BIGINT` column, a decimal or a string in an integer one), a NULL in a column the plan reads as non-null (counted on the data, since `con.put` tables are nullable by default), and an integer outside its declared type's range when the table's physical type is wider (an `int64` column read as `int32`; the engine counts the values outside, once, as a precondition). Narrower integers, `float32` in a double column and a nullable column without NULLs still run. Strings of any Arrow width count as one type. Before, `Report.run` checked none of this and only Polars's reader refused a changed type, so a run on drifted data returned rows that broke a postcondition the report calls proved ([#1540](https://github.com/AlexanderNenninger/substrait-lean/issues/1540)).

### The schema check covers pipelines, incremental views and `run_sharded`

The check `Report.run` makes on its tables (types, NULLs in a non-null column, integers outside their declared width) now also runs where a plan reads tables outside a report: `run_sharded` refuses a shard or broadcast table that differs from the plan's schema (`ValueError`), and an incremental view checks its tables when it is built and the rows each batch inserts (`PreconditionError`). On an Arrow table the width check is one native pass over the column's minimum and maximum instead of a counting plan on the engine: 5 million rows take 0.8 ms where the plan took 95 ms ([#1540](https://github.com/AlexanderNenninger/substrait-lean/issues/1540)).

### A redelivered duplicate no longer takes a published row out of the sink

With `on_violation="quarantine"` and a `unique` key, an exact copy of a row the node already holds sent both copies to quarantine and deleted the published row. Rows identical in every column now count once: the kept row stays and the extra copy is set aside. Copies that disagree on some column still go to quarantine together ([#1547](https://github.com/AlexanderNenninger/substrait-lean/issues/1547)).

### Engine packages check their sverify

`sverify-duckdb`, `sverify-polars` and `sverify-spark` check at import that the installed `sverify` speaks their plugin interface, and otherwise fail with one `ImportError` that says to install both from the same release, in place of a `TypeError` from deep inside sverify (#1585). `sverify check` no longer prints a second traceback when `sverify.errors` itself fails to import; it exits 8 with the message.

### sverify-dbt first run

A seed without `column_types` is checked once `dbt seed` and `dbt docs generate` have given it types, and is refused with that instruction before (#1586). The refusal for a relation without types now reads "ref('x') has no column types: …", and `sverify-dbt suggest` says when it read nothing because every model was refused. A plain `dbt compile` after `dbt run` renders an incremental model's `{{ this }}` branch; sverify-dbt now says so and asks for `dbt compile --full-refresh`.

### Quarantine report: published rows a disagreeing duplicate took out

`QuarantineReport` gains `retracted`: of the rows a refresh quarantined, how many the node had already published, because a new row repeated their key with other values. The report line says "N already published", and the refresh JSON has a `retracted` field per source ([#1593](https://github.com/AlexanderNenninger/substrait-lean/issues/1593)).

### `VAR_*`, `STDDEV_*` and `COVAR_*` read `float_overflow`

The function groups `agg.var` and `agg.stat` now list `float_overflow`, as
`agg.fsum` does, so each engine's table states what it gives where a
variance or covariance of finite doubles overflows: `+inf` on DuckDB, Polars
and Spark (their facts' new probes,
[#1601](https://github.com/AlexanderNenninger/substrait-lean/issues/1601)). The
reference already raises there (`AggFn.infAgg`); a `#guard` in
`Infer.lean` now ties the two lists. Results are unchanged.

### Main carries a development version

A build from main is versioned `<next minor>.0.dev0` (now `0.9.0.dev0`), so it cannot be mistaken for the release on PyPI, and an `==` pin no longer matches across the two. `python/scripts/set_version.py` sets the nine places that carry the version; the release skill uses it for the bump and to reopen main after a release (#1606).

### DuckDB's integer mean depends on the plan's shape and the platform

DuckDB rewrites an ungrouped `avg` of integers to `SUM / COUNT`, which gives the model's value. A grouped or window `avg` keeps the native finalize, which on x86-64 Linux divides in 80 bits and rounds again, so its last bit can differ from the model's. The negative-sum cast of `HUGEINT` to `DOUBLE` rounds twice on every platform. The probes `avg_int.py` and `avg_int_shapes.py` count both, and the fact `duckdb-avg-int` records them
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

### A repeated guarded double operation is computed once

The guards of a double operation repeated the operation's SQL, and nested operations multiplied
it: `(x * x + x) / y` wrote 579,251 characters. A projection of double arithmetic
(no branch or short-circuit, so every part is evaluated on every row anyway) now computes
each such operation once, in a layer below it. The same query writes 3,528 characters and
runs in 0.011 s on 3 million rows in DuckDB, against 0.657 s
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

### The refusal of `CAST(DOUBLE AS BIGINT)` no longer advises `round()` first

Under `semantics="duckdb"` the lift refuses `CAST(x AS BIGINT)` of a double, since DuckDB
rounds half to even and the model's cast truncates. The message advised `round()` first,
but the lift refuses that composition too. It now says to use `semantics='reference'`
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

### Guards that a constant decides are not written

A literal operand decides checks that the written SQL used to spell out: `x / 2.0`
no longer carries the division-by-zero, infinity-over-infinity and overflow
`CASE`s (2680 characters become 244), and `n // 10` drops the sign tests of the
floor division and the zero check that never held (1390 become 438). A check
stays where a constant can still make it fire (`x / 0.5` can overflow)
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

### `COUNT(DISTINCT x)` is written natively

The written SQL counts the distinct values of a non-double column with the
engine's own `COUNT(DISTINCT x)`, not a `ROW_NUMBER` over the group and the
value ([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).
On 5 million rows it takes 0.08 s, down from 0.30 s.

### A row cap bounds a `COUNT`

With `sv.max_rows(n)` on its input, a `COUNT` is proved to be at most `n`, as an
integer `SUM` already was. A query that multiplies or adds a count now proves
its result fits `BIGINT` from a bound on the column and a row cap. This covers
the exact exit of a threshold computed from the data, `x * COUNT(y) > SUM(y)`,
which the refusal of `x > (SELECT AVG(y) …)` names ([#1608]). Without a cap the
product still has an `overflow` error.

[#1608]: https://github.com/AlexanderNenninger/substrait-lean/issues/1608

### Shorter, faster range checks in written date SQL

The SQL Sverify writes for `date_trunc` of a date and for a date plus a constant number of days now checks the reference's date range once, on the input: a truncation stays in range, and a constant shift moves the range. On DuckDB, `date_trunc('month', day)` over 5 million rows runs 2.4× faster (0.085 to 0.035 s), and `day + INTERVAL 7 DAY` matches the hand-written query. The results and the errors are the same ([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

### Date and time operations compute their operand once

The range guards of a date or timestamp operation (`day + INTERVAL 7 DAY`,
`date_trunc('month', day)`, `date_part`) repeated the operand's SQL, and the
`DATE` as `TIMESTAMP` guard nested them. A projection of date and time
operations over columns now computes each operand once in a layer below it:
`day + INTERVAL 7 DAY` writes 1,326 characters instead of 3,227 and
`date_trunc('month', day)` 1,366 instead of 3,387, and on 10 million days in DuckDB they run in 0.08 s
instead of 0.12 s and 0.41 s instead of 0.69 s
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

### A mean of a bounded integer column is exact

A double `SUM` or `AVG` of an integer column whose values are at most `M` in
magnitude, over at most `N` rows with `N · max(M, 1) ≤ 2^52`, is now exact on
every engine: every summation order adds such integers exactly, and a mean
divides once, as the reference does. Its column reports no tolerance, so a
threshold on it, such as `qty > (SELECT AVG(qty) FROM orders)` with a bound on
`qty` and `sv.max_rows`, lowers instead of being refused ([#1608]). D35 is
amended for the summation orders Sverify takes on trust (DuckDB's constant
runs, Polars's in-memory Kahan sum), with each engine's tests as evidence.

[#1608]: https://github.com/AlexanderNenninger/substrait-lean/issues/1608

### The written SQL leaves ties open, as the reference does

Under the default observation (`rows="multiset"`), `report.to_sql` and
`node.to_sql` no longer number rows by `rowid` to break ties as Lean's list
order does. A sort, a `LIMIT` and a window below it use the sort keys alone;
the result is ordered only where the plan's last sort orders it. Plans with
open ties no longer return `Rel.eval`'s rows on every run unless the report is
`reproducible` or `rows="sequence"` asks for them. On 3 million rows in
DuckDB the survey's window queries run 1.8 to 2.1x faster
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

### `suggested_requires` states the bound a hint names

A refusal that proves once a bound is stated now puts that bound in
`report.suggested_requires`: `_.total.between(-1e300, 1e300)` for a `SUM` or
`AVG` of a double (also behind a join or a CTE) and the integer bounds of a
`LAG` overflow. `requires=report.suggested_requires` proves them
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

### The threshold refusal names the exit for a mean

`a filter, grouping key or sort on a double may keep other rows` now says what to do for each kind of threshold: a constant takes a
precondition that keeps the values away from it, and a threshold computed from the data
(`qty > (SELECT AVG(qty) …)`) takes exact columns, for a mean of integers `x * COUNT(y) > SUM(y)`,
which is the exact mean's comparison and another query than the rounded one
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

### `ORDER BY ... LIMIT n` is written as a top-N

The written SQL sorts and limits in one SELECT, which DuckDB runs as a Top N,
and numbers only the rows that stay. It no longer numbers the whole table
first: on 5 million rows `ORDER BY total DESC, id LIMIT 10` takes 0.015 s,
down from 0.455 s
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

### A grouped double `SUM` or `AVG` runs faster on DuckDB

Sverify checks a double `SUM` or `AVG` for both infinities among its values and for finite values that overflow. On DuckDB it now runs those checks only for the groups whose sum is not finite, in a second stage joined back on the keys (#1608, #1787). On 10 million rows the written query takes 0.11 s where it took 0.37 s, and 0.23 s where it took 0.46 s behind a join; with every group infinite it takes the same time as before.

A finite sum has finite values. Lean proves this for sums added in any tree or in sequence (`SumOrder.isFinCode`). For DuckDB's constant runs and Polars's compensated sum it is a probed engine fact (`duckdb-sum-double`, `polars-sum-float`). The two-stage SQL is tested against the one-stage SQL (`tests/test_two_stage_sums.py`). The group keys stay as written; doubles as keys, window sums and the other engines keep one stage.

### Tied windows, `first` and `string_agg` take their keys alone

Under `rows="multiset"` a window node with two or more functions that read
how ties are ordered numbers its rows once, so every function sees one
arrangement (`Rel.Allowed`'s). `first`, `last`, `string_agg` and `collect` sort
by their own keys, without the row ordinal. Spark and Snowflake write plans with
tied windows and `LIMIT`s that they refused, and `rows="sequence"` is the only
observation they still refuse. Where an engine's runner leaves ties open (`ProfilePlugin.rows`, Spark and
Snowflake), a margin check above a `LIMIT` or a window that reads the order of
ties is refused before the run, since the check and the run would each pick
their own rows; `reproducible=`, a total sort key or `on_inferred="warn"` lift
it. DuckDB writes both statements with the row ordinal and is not affected
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

### `CAST(round(x) AS BIGINT)` of a double lifts from DuckDB SQL

Under `semantics="duckdb"`, `sv.sql` now lifts `CAST(round(x) AS BIGINT)`,
and the same with `floor` and `ceil`, where `x` is a `DOUBLE`. Sverify proves
the lifted plan computes what DuckDB does: the rounded value is integral, so
DuckDB's half-to-even cast and the model's truncating cast agree, and NaN,
±∞ and values past 2⁶³ raise in both. A bare `CAST(x AS BIGINT)` of a double
and casts to narrower integer types stay refused; the bare cast's refusal
names the rounded casts that lift
([#1655](https://github.com/AlexanderNenninger/substrait-lean/issues/1655)).

### A deep `AND`/`OR` nest in a filter or projection checks in time linear in its depth

Beyond the top three levels, a filter's `AND` and `OR` chains are now bound as
guarded columns below the filter, one projection per operand that may raise,
each operand written once (D50-d,
[#1719](https://github.com/AlexanderNenninger/substrait-lean/issues/1719)).
The same holds for a projection's expressions. The plan keeps the lift's rows
and raises where it raises (`Rel.guardedFilter_eval`, `Rel.guardedFilter_raises`,
and the projection's), and a guard below the third level is proved where the
analysis already reads it, in the level's `CASE` condition. Elsewhere
(aggregates, join conditions, lambdas) the levels below the third stay eager,
as before.

On Spark 4.3, Spark's parser refuses the SQL sverify writes for an alternating
nest 80 levels deep (299 KB) and nothing runs; 70 levels (231 KB) parse and run
in 16 to 31 s, most of it in Spark's optimizer (measured on homelab,
[#2030](https://github.com/AlexanderNenninger/substrait-lean/pull/2030#issuecomment-7056408687),
[phases](https://github.com/AlexanderNenninger/substrait-lean/pull/2030#issuecomment-7057113974)).
Sverify sets no depth limit of its own.

### UTC instants: the conversion with a naive timestamp, and instant literals

A timestamp with the time zone UTC (an instant, [D53](docs/decisions.md#d53-a-timestamp-with-the-time-zone-utc-is-an-instant)) can now be converted to and from a naive timestamp at UTC, which keeps the microseconds: `x AT TIME ZONE 'UTC'` in SQL, the cast between `timestamp('UTC')` and `timestamp` in Ibis. A literal with an explicit offset is an instant (`TIMESTAMPTZ '2024-01-01 12:00:00+02'`, a timezone-aware Python `datetime`), so a filter by an instant, `IN` over instants and `COALESCE` with one run on DuckDB and Polars, under any session or host zone, and a Delta filter on an instant skips the files its naive twin skips. A literal without an offset, DuckDB's `CAST` between the two kinds, and a comparison, `IN`, `COALESCE`, `CASE` or set operation that mixes an instant with a naive timestamp are refused and name [#1725](https://github.com/AlexanderNenninger/substrait-lean/issues/1725), because DuckDB reads them in the session's zone. Calendar functions of an instant stay refused. `UnFn.atUtc` is new in the core, so the DuckDB lowering is regenerated.

### A UTC-zoned timestamp is read as an instant

A Delta `timestamp` column (Arrow `timestamp[us, tz=UTC]`) is no longer refused. It is an instant, its own kind ([D53](docs/decisions.md#d53-a-timestamp-with-the-time-zone-utc-is-an-instant)): compared with another instant, ordered, grouped, joined on, aggregated with `MIN`, `MAX` and `COUNT`, and written back as an instant (Delta `timestamp`) on DuckDB and Polars, whatever the session or host time zone. Calendar functions, interval arithmetic, casts, a naive timestamp in the same comparison, literals and zones other than UTC are refused and name [#1725](https://github.com/AlexanderNenninger/substrait-lean/issues/1725); Spark and Snowflake refuse the kind until they have a map. The conversion to a naive timestamp and instant literals are the next step of the issue.

### DuckDB reads partitioned and column-mapped Delta tables, and Delta tables on S3, where they are

A Delta table's partition values come from its log, and its column mapping (by name or by id) is followed, so DuckDB scans these tables without loading them into Python (#173). Delta tables on S3 are read through DuckDB's `httpfs` with a temporary secret made from the `Storage`; with no explicit key the scan needs DuckDB's `aws` extension, and without it the table reads through Arrow as before.

Also fixed: the Arrow route returned NULL for every column of a column-mapped Delta table, because delta-rs's Arrow reader ignores the mapping. It now reads those tables through delta-rs's DataFusion reader, and their file statistics reach the logical columns.

### DuckDB reads renamed Iceberg columns and equality deletes natively

An Iceberg table's Parquet files are read by field id, so a column renamed since a file was written is found without passing the table through Python. Equality deletes (which pyiceberg cannot read) apply to the data files written before them, NULL matching NULL, for local Parquet files of tables without partition fields ([#173](https://github.com/AlexanderNenninger/substrait-lean/issues/173)).

### Polars reads partitioned and column-mapped Delta tables from their files

A Delta table with partition columns or column mapping (by name or by id) on Polars is scanned lazily on its streaming engine, as on DuckDB, instead of reaching Polars as an Arrow copy: the partition values from the log are joined on the file path and the files are read by their physical names ([#173](https://github.com/AlexanderNenninger/substrait-lean/issues/173)).

### Polars reads Delta and Iceberg tables from their files

A pipeline on Polars holds a local Delta or Iceberg source as the Parquet files of its version, and Polars scans them lazily on its streaming engine instead of receiving an Arrow copy of the table. Deletion vectors, position and equality deletes and renamed Iceberg columns are applied as on DuckDB, and a file column whose type does not widen to the table's raises ([#173](https://github.com/AlexanderNenninger/substrait-lean/issues/173)).

### Internal: a Parquet scan is plain data, and DuckDB's reader of it lives in `sverify_duckdb`

`sverify._scan.Scan` no longer holds SQL: `sverify_duckdb.scan` reads a scan (`attach_scan`, `read_scan`), as the Polars and Spark plugins will read it (#173). `Scan.to_arrow()` stays the reference reader. No behaviour changes.

### Spark reads Delta and Iceberg tables from their files

A plan run on Spark reads a local Delta or Iceberg source as the Parquet files of its version, with the session's own reader, instead of receiving an Arrow copy of the table through `createDataFrame`. Deletion vectors, position and equality deletes and renamed Iceberg columns are applied as on DuckDB and Polars, and classic and Spark Connect sessions both work ([#173](https://github.com/AlexanderNenninger/substrait-lean/issues/173)).

### A decision on DuckDB's integer `AVG` is refused where DuckDB may take it the other way

Under `semantics="duckdb"`, DuckDB's own `avg` of integers returns a double
within a band of the mean Sverify verifies
([#1735](https://github.com/AlexanderNenninger/substrait-lean/issues/1735)).
The lift marks that mean (D52), and a plan that reads it is proved only where
every filter, sort, `DISTINCT`, join condition, grouping key, postcondition and
key that reads the mean has one outcome over the band, and every output column
that reads it has a bound in `Report.epsilon`. Elsewhere the report holds a
`source_threshold` error and its verdict is `unproved`, so `to_sql`, `run`, the
SQL-file CLI and sverify-dbt refuse it. The way out is a precondition that keeps
the mean away from the threshold, or exact columns: `SUM(y) > c * COUNT(y)` for
an integer `c`.

### GROUP BY ALL over a FROM-first query names itself

`FROM t GROUP BY ALL` (DuckDB's FROM-first form, which selects `*`) is refused with "GROUP BY ALL over `*` ... name the columns in a SELECT" instead of "`*` is not supported yet" (#176).

### A Polars connection needs no DuckDB

`sv.connect("polars")` holds its tables as Arrow and runs with no `duckdb` installed (#1764), and the `polars` extra no longer brings `sverify[duckdb]`. Without DuckDB, an Ibis expression bound to such a connection (`con.table(name)`) does not execute through Ibis: it names the engine to run on (`Report.run(con, "polars")`). With DuckDB installed it executes there as before. Spark does not hold tables (a connection runs on DuckDB or Polars), so the `spark` extra keeps `sverify[duckdb]`.

### Table conditions are counted by the engine that runs their plan

`unique`, `references`, `rows_per`, `max_rows` and `arrives_within` were counted by executing an Ibis expression on the connection's own backend (DuckDB). Each is now an Ibis relation that the checker's plan carries, run by the engine the check runs on, with the reference's meaning; a NULL key is one key in `unique` and `rows_per`, a NULL foreign key breaks nothing in `references`, on DuckDB, Polars and Spark. All the table conditions of one table run as one plan. A condition the engine's writer refuses refuses the check (#1764).

### An integer cast gives the type it names

`t.a.cast("int32")` is an `int32` in `Report.output` and in the run, on every
engine, and so is a widening cast such as `t.b.cast("int64")` of an `int16`
column. Both were `int64` and `int16` before
([#1772](https://github.com/AlexanderNenninger/substrait-lean/issues/1772), ruling 114).

### Every refusal of the Ibis producer names its construct

Each refusal of the Ibis frontend sets `UnsupportedError.construct`: `"function <name>"` for a function, otherwise SQL keywords in upper case (`"LAMBDA"`, `"FRAME"`, `"INTERVAL"`, `"JOIN"`). A tool can group refusals by it without reading the message, whose text is unchanged ([#700](https://github.com/AlexanderNenninger/substrait-lean/issues/700), [#1786](https://github.com/AlexanderNenninger/substrait-lean/pull/1786)).

### Precondition checks count in Arrow

A run that checks its preconditions on an engine counted each condition's failing rows in a Python loop over every row. It now counts them with Arrow's compute kernels. On the catalogue's `fin-vwap` at 10⁶ rows, the preconditions take 10 ms where they took 121, and the checked run on DuckDB 98 ms where it took 212 (#1787).

### No overflow assumed for a division by a decimal

A double divided by a decimal converted to a double, such as `price / CAST(quantity AS DOUBLE)` with a decimal quantity, no longer assumes an overflow to `±inf` where the dividend is bounded. A zero divisor raises division by zero first. Any other decimal at scale `s` is at least `10⁻ˢ` in size, so the quotient stays within the dividend's bound over that divisor (`decQuotFinite_sound`, #1787).

### No overflow check on a division by a count

A double divided by an integer cast to a double, such as a rate `d1.cast("float64") / users` or a mean computed as a sum over a count, can't overflow to `±inf`. A zero divisor already raises division by zero, and any other divisor is at least 1 in size. Sverify proves this (`Expr.mayInfBin_sound`), so it no longer assumes such an overflow or checks for it in the SQL it writes (#1787).

### A verified run on DuckDB leaves out checks the proof rules out

Where the contract's preconditions rule out an expression's errors, a verified run on DuckDB now writes that expression without its checks, the check that a double operation does not overflow to `±∞` included (#1787). The run checks the preconditions on its tables first, and only a run whose preconditions were checked, on a route through the reference, does this. Lean proves the expressions meet no issue there (`Expr.issues_nil_of_safe`, `Rel.duckdb_marks`). As on Polars, this rests on the data not changing between the input check and the run. `to_sql` keeps every check unless given a report's `unchecked`.

### A verified run leaves out the row numbering the result doesn't need

To give the rows in Lean's order, a run on DuckDB or Polars numbers them, and DuckDB first copies each input to do so. Where the checker proved that the observation can't see that order, a verified run now leaves the numbering out (#1787). Under the default multiset lens this holds when the result is deterministic (`check_deterministic_sound`). Under `rows="sequence"` it holds when the plan's last sort decides every row's place (`check_sequence_determined_sound`). This happens only on a run that checked the preconditions on its tables, on a route through the reference. `Report.to_sql` already wrote SQL this way for a multiset lens.

### A pending engine profile keeps the reference's ±∞ precondition

`verify(semantics="polars")` (or Spark's), whose report is the reference's
until the engine has a report of its own, dropped the reference's
precondition that no double overflows to ±∞ while labelling the report
`"reference"`. It now keeps it, as the reference's report does. Only
`semantics="duckdb"`, DuckDB's SQL lift, treats ±∞ as the value (#575).

### A bounded double `SUM` runs without its overflow checks

A double `SUM` or `AVG` whose column is bounded, over an input with a `max_rows` cap, can't overflow to `±∞` in any order an engine adds it (#1787). A verified run on DuckDB now writes it as a plain sum, without the second pass that checked for `±∞`. As with the other run-time checks, this happens only on a run that checked the preconditions on its tables. Sverify's bound for engine sums now also reads `-0.0` as zero (D35, amended).

### Proved rewrites run on an engine, in Lean

Sverify's Lean model now states what an optimization must prove before an
engine may run it ([#1787](https://github.com/AlexanderNenninger/substrait-lean/issues/1787), step 1).
A rewrite that refines the plan, exactly or up to the order of rows, gives an
engine run that the reference allows for the plan as written
(`Engine.Sound.of_refines`). A contract verified on the plan as written holds
on that run, with every bound computed from the written plan
(`Engine.contract_sound_rewrite`). A refinement at one node carries up through
every operator but `FETCH` (`analysis/Sverify/Analysis/Refines.lean`), and
`Engine.runPlan` falls back to the written plan when the engine does not
translate the rewrite or the rewrite fails the side condition's check. Nothing
runs the optimized plan yet: item 2 of the epic adds the per-rule gate.

### Seven proved rewrites run by default

`Report.run` now runs the rewritten plan where one of seven proved rewrites
applies and the run checked your preconditions on the data
([#1787](https://github.com/AlexanderNenninger/substrait-lean/issues/1787),
ruling 150): an implied filter, a filter the contract rules out, `DISTINCT`
or `GROUP BY` on a key, `fn(DISTINCT key)`, and a join to a keyed table none
of whose columns the query reads. The engine gets other SQL for those plans,
and under `rows="multiset"` the rows may come back in another order.
`run(check_requires=False)`, `run(optimize=False)` and `Report.to_sql` keep
the plan as written; `to_sql(optimize=True)` writes the rewrite, for data you
know meets the preconditions. The name `optimize` is provisional. The report's
`run_gate` says when the checker kept the plan as written. The bench and the
rules that stay off are in `docs/optimizations.md`, "The gate".

### Proved rewrites can run, rule by rule

Sverify can now run the rewritten plan in place of the plan you wrote, where
the checker proves the rewrite keeps the guarantee
([#1787](https://github.com/AlexanderNenninger/substrait-lean/issues/1787),
item 2). A gate turns each rewrite rule on or off, and a rule goes on only
with a measured gain and no loss on DuckDB, Polars or Spark
(`docs/optimizations.md`, "The gate"). `Report.run` and `Report.to_sql` take the
checker's plan to run on the translated and transfer routes. Elsewhere they run
the plan as written, as they do wherever a gate keeps it: the report names that
gate. Every rule starts off, so no result or written SQL changes.

### No overflow assumed where a division or product shrinks its operand

Sverify proves that a double divided by a value of at least 1 in size, or multiplied by one of at most 1, can't overflow to `±inf` (`BinFn.shrinks_fin`). Two common examples are a percentage `x / 100.0` and a rate `x * 0.01`. The same holds when a contract's ranges bound the divisor or factor, as in `x / y` with `y >= 1`. Sverify no longer assumes an overflow there, so a checked run drops the assumed check before the plan and the check in the SQL it writes (#1787).

### Written plans declare only the functions they call

A plan the checker writes (`--write`, a report's `optimized`, the plan to run and the assumed issues' check) used to declare all 153 functions sverify knows, about 11 KB of each plan. It now declares only those it calls, so a written plan is 0.6–3.3 KB where it was 11–13 KB, and the contract goldens' answers are 75 KB where they were 190 KB (#1787). A plan's digest is unchanged: it never read the declarations (`plan_digest`).

### Every refusal of the SQL lift names its construct and the SQL it refused

Each refusal of the SQL frontend sets `UnsupportedError.construct` (`"function md5"`, or keywords such as `"CORRELATED SUBQUERY"` and `"TRY CAST"`) and `UnsupportedError.sql`, the innermost part of the query being read, cut at 60 characters. With #1786 every refusal of both frontends names its construct ([#700](https://github.com/AlexanderNenninger/substrait-lean/issues/700), [#1788](https://github.com/AlexanderNenninger/substrait-lean/pull/1788)).

### Polars keeps the sign of a zero (D31)

The Polars engine made `-0.0` read as `0.0` and canonicalised scalar results, so a plan such as `cot(x)` for a row `x = -0.0` returned `+inf` on Polars where the reference and DuckDB give `-inf`. Reads and scalar results now keep their raw values, as the SQL writers do (#1461); only identity boundaries (comparison, group, join and window keys) read the zeros as one. A sum or difference gets IEEE's zero sign by a shim (`polars-zero-sign`), and so does `x ** y` (`(-0.0) ** 0.5` is `+0.0`). A double group key is the canonical zero (#1794).

### A double product's domain error names its cause

A product `x * y` of unbounded doubles is reported as a domain error (`0 * ±inf` is NaN), with the hint to bound the columns. With finite bounds the verdict is `proved_with_checks`: the overflow to `±inf` is checked on the data ([#1803](https://github.com/AlexanderNenninger/substrait-lean/issues/1803)).

### `STDDEV_*` bounds are proved

`Report.epsilon` of a `STDDEV_*` column of doubles is now proved on DuckDB
and Spark, as `VAR_*` and `COVAR_*` already were: an engine's square root of
its variance is within the reported bound of the reference's correctly
rounded root (`FloatBounds.StdModel.epsilon_stddev_cr`,
[#1807](https://github.com/AlexanderNenninger/substrait-lean/issues/1807)).
Polars stays tested until its `VAR_*` algorithm is proved (#1808).

### The covariance proof is stated for any merge

The covariance's error invariant is now proved for any merge of pairs that meets
`CMergeSpec` (`cInv_merge_of`), over the bound's constants (`CConst`), with
DuckDB's merge as one instance at its own constants (`chan_spec`,
`CConst.chan`). This is the first step toward proving Polars's `COVAR_*` and
`CORR` (`stat_algo`), whose merge is Schubert and Gertz's
([#1808](https://github.com/AlexanderNenninger/substrait-lean/issues/1808), ruling 271).

### Polars's `COVAR_*` and `CORR` rows are proved

Polars's `CORR` is now proved within `StatProps`' bound, at the same constants
as DuckDB's (`FloatBounds.StdModel.core_corr_polars`,
[#1808](https://github.com/AlexanderNenninger/substrait-lean/issues/1808),
ruling 271). Polars's `agg.stat` `stat_algo` row, which `COVAR_*` and `CORR`
share, is now proved, so `proved_on` lists Polars for `COVAR_*` columns.

### Polars's `COVAR_*` bound is proved, with a looser leading constant

Polars's `COVAR_*` is now proved within `StatProps`' bound at Schubert and
Gertz's constants (`stat_algo` `SCHUBERT_GERTZ`, `StatTol.sg`,
`FloatBounds.StdModel.core_cov_polars`,
[#1808](https://github.com/AlexanderNenninger/substrait-lean/issues/1808),
ruling 271). Its leading constant loosens from 71 to 107, so a plan whose
stated tolerance sits between the two can change from verified to not verified
on Polars. DuckDB's and Spark's bounds are unchanged. Polars's `COVAR_*` and
`CORR` share one `stat_algo` row, which stays tested until Polars's `CORR` is
proved.

### Polars's `VAR_*` and `STDDEV_*` bounds are proved

`Report.epsilon` of a `VAR_*` or `STDDEV_*` column of doubles is now proved on
Polars as on DuckDB and Spark: two-pass blocks, Welford's update and Schubert
and Gertz's merge, in any order and tree, keep the variance within the
reported bound (`FloatBounds.StdModel.core_var_polars`,
[#1808](https://github.com/AlexanderNenninger/substrait-lean/issues/1808)).
`proved_on` lists Polars for `VAR_*` and `STDDEV_*` columns. Polars's `COVAR_*`
stays tested against a fuzzed bound.

### The corrected two-pass bound is proved

`FloatBounds.StdModel.corrTwoPass_error` bounds the textbook formula
`Σ d² − (Σ d)² / n` applied to doubles shifted by any constant, which is how
sverify writes Snowflake's `VAR_*` (values minus their group's mean), with
both sums added in any order an engine may use
([#1810](https://github.com/AlexanderNenninger/substrait-lean/issues/1810)).
For the group's mean the bound is `(2n + 9) u S` to first order.

### Errors name the missing extra

A call that names an engine sverify installs as an extra, when that engine is
not installed, raises `ImportError` with the install command:
`sv.connect("polars")`, `sv.verify(..., semantics="polars")`,
`report.run(con, "polars")` and `sverify.sql.dialect_of("spark")` say
`engine 'polars' is not installed: pip install 'sverify[polars]'`, where they
said "unknown engine"
([#183](https://github.com/AlexanderNenninger/substrait-lean/issues/183)). A
test checks every entry point of an extra on a bare install.

### sverify-dbt reads dbt's files as UTF-8 on every platform

`sverify-dbt` names `encoding="utf-8"` where it reads dbt's `manifest.json`
and the selectors file it writes, so a project with non-ASCII names or
descriptions reads the same on Windows as elsewhere
([#183](https://github.com/AlexanderNenninger/substrait-lean/issues/183)).

### Text files are read and written as UTF-8 on every platform

sverify names `encoding="utf-8"` wherever it reads or writes a text file: the
SQL files of `sverify check`, ODCS contracts, OpenLineage files, sink records,
secrets files and the proof cache. On Windows, Python's default is the
locale's code page (cp1252), so non-ASCII text in those files failed or was
misread there
([#183](https://github.com/AlexanderNenninger/substrait-lean/issues/183)).

### The CLI's time budget stops cleanly where there is no SIGALRM

On Windows, `sverify check --timeout` (and `SVERIFY_TIMEOUT`) now raises the
budget's error in the main thread when time runs out, so the command prints
what it proved before stopping, as on Linux and macOS. Before, only the
watchdog stopped it, ending the process without the partial report
([#183](https://github.com/AlexanderNenninger/substrait-lean/issues/183)).

### Windows paths in table names, file URIs and `check --fix`

Three fixes from the Windows trial
([#183](https://github.com/AlexanderNenninger/substrait-lean/issues/183)):

- A Delta source at a Windows path (`C:\lake\orders`) is named `orders`. It
  was named after the whole path, so a refresh, its sink record and a resume
  looked it up under another name.
- A `file:` URI keeps its drive and host: `file:///C:/db/t` and
  `file://C:\db\t` are read under `C:`, where native scans (DuckDB, Polars,
  Spark) looked under the current drive's root.
- `sverify check --fix` and `--diff` keep a file's line endings. A file with
  `\r\n` endings came back with `\r\r\n` on Windows, and `--diff` showed
  every line as changed.

### Fixed: Spark's IEEE division by `-0.0`

A division of doubles under `on_division_by_zero` = `IEEE` (what `semantics="duckdb"` asks for) returned the opposite infinity on Spark for a `-0.0` divisor: `1 / -0.0` gave `+inf` where the reference gives `-inf`, in every release since 0.2.0. Spark now writes the plain `/`, so an IEEE division by a zero of either sign raises on Spark (`DIVIDE_BY_ZERO`), as Spark's engine model states; DuckDB SQL with a zero divisor raises there where DuckDB returns `±inf`. Snowflake's division was the plain `/` already.

### Fixed: a rounded, cast or compared double that an engine computes within a bound

A projection that sends a double through `floor`, `round`, a cast to an integer,
a decimal or text, or a comparison was PROVED on an engine that computes the
double only within a bound, and could return another integer or truth value
there: `floor(x / 49.0)` was `0` on Polars, whose quotient by a constant lands
one ulp below `1`. Such plans are now refused on those engines, as a filter on
the same double is (#568's threshold rule), and run where the double is exact;
a precondition that keeps the value away from the threshold lifts the refusal
([#1849](https://github.com/AlexanderNenninger/substrait-lean/issues/1849), ruling 275).

### A report read back keeps its run-time checks

`Report.to_json` now writes what a run checks on the data (the margin checks of threshold filters on double sums, the pair counts of as-of joins and the as-of join's cap) and `Report.from_json` reads it back; a plan read by `Report.from_substrait` keeps the cap ([#1863](https://github.com/AlexanderNenninger/substrait-lean/issues/1863)).

### An integer cast to a wide DECIMAL is read as a decimal (corrected rule)

Sverify used to read an integer's cast to `DECIMAL(p, 0)` with 19 or more digits as the integer itself, a rule from before decimals were modelled. Arithmetic after such a cast was then checked and written at 64 bits, where the plan computes it at `p` digits: `CAST(i AS DECIMAL(38, 0)) * j` was reported as `may fail: overflow` and refused ([#1876](https://github.com/AlexanderNenninger/substrait-lean/issues/1876)). The cast is now read as the plan declares it, as any other cast to a decimal:

- arithmetic after the cast is checked at `p` digits, so such products and sums prove where they fit;
- the result column is `DECIMAL(p, 0)` where it was an integer;
- the public Snowflake writer, which computes no decimal as the reference does yet (#27), refuses such a plan where it wrote 64-bit integer arithmetic before.
- a decimal's truncation and rounding to an integer keep their operand's bounds, so more casts of a decimal back to an integer prove: `CAST(CAST(i AS DECIMAL(38, 0)) AS BIGINT)` proves with no precondition.

### Long IN lists check in milliseconds

The checker's time for `x IN (...)` grew exponentially with the list's length:
2.5 s for 11 literals, minutes for 13. Checking each `OR`'s right operand
re-analysed the left one several times, and an `IN` list nests its `OR`s on
the left. A list of 50 literals now checks in under 0.1 s
([#1877](https://github.com/AlexanderNenninger/substrait-lean/issues/1877)).

### ODCS: `missingValues` rules that list values read

`odcs.read` raised `TypeError` on a `missingValues` rule that listed values. It now reads the rule as the column being neither NULL nor one of the values (#1886).

### ODCS: a fractional row cap reads

`odcs.read` reads a `rowCount` cap such as `mustBeLessOrEqualTo: 2.5` as `max_rows(2)`, where it used to skip it as a lower bound.

### to_substrait casts the narrower input of a set relation

A set relation whose inputs differ in decimal precision (a full outer join of two sums) is written with a cast of the narrower input to the wider precision at the same scale, and reads back (#1904). It was refused for the time between #2106 and this change.

### Substrait export: a set relation whose inputs differ in type is refused

`to_substrait` refuses a plan whose set relation has inputs of different column types, decimals of two precisions for example, which Substrait does not allow. It used to write a plan the Substrait validator rejects (TPC-DS q51). `report.to_sql(dialect)` writes the plan for an engine.

### float32 columns, interval casts, and unread columns under SQL conditions

- Sverify reads float32 (`REAL`) columns and constants: it passes them through,
  compares, orders and groups them, takes their `min` and `max`, and casts them
  to double. A run returns float32 where `Report.output` says float32, on every
  engine, and a float32 constant arrives bit for bit. Every use whose result
  depends on the width stays refused with the step named: arithmetic, `SUM`, `AVG`
  and the statistical aggregates, `round`, and casts to strings, decimals and
  `REAL` ([#1908](https://github.com/AlexanderNenninger/substrait-lean/issues/1908),
  [#417](https://github.com/AlexanderNenninger/substrait-lean/issues/417), ruling 186).
- In SQL, a `REAL` next to an integer or decimal constant is compared as a `REAL`, as
  DuckDB does (`0.3::REAL = 0.3` is true; fact `duckdb-coerce-real`). The constant is
  rounded once, as DuckDB rounds it; one that would round twice (an integer past 2^53,
  a decimal whose nearest double is halfway between two singles) is refused.
- A double constant `-0.0` keeps its sign in the written plan and on Polars.
- An integer cast to an interval of weeks, days, hours, minutes or seconds,
  `n.cast("interval('D')")`, is read as `n.as_interval("D")`
  ([#1926](https://github.com/AlexanderNenninger/substrait-lean/issues/1926)).
- A SQL `ensures` condition on an Ibis transformation no longer fails on a binary
  or map column that nothing reads
  ([#1958](https://github.com/AlexanderNenninger/substrait-lean/issues/1958)).
- Binary values are refused by design, with advice that holds on every engine:
  encode them as text at the source (hex or base64), or leave the column out
  ([#1918](https://github.com/AlexanderNenninger/substrait-lean/issues/1918)).

### Aggregates and windows over expressions

`mode()` of an expression ([#1909](https://github.com/AlexanderNenninger/substrait-lean/issues/1909)), window partitions and sort keys that are expressions ([#1930](https://github.com/AlexanderNenninger/substrait-lean/issues/1930)), `quantile()` of several fractions ([#1910](https://github.com/AlexanderNenninger/substrait-lean/issues/1910)) and `nunique()` of whole rows ([#1912](https://github.com/AlexanderNenninger/substrait-lean/issues/1912)) are read: the Ibis producer projects the expressions into columns first, writes one measure for each fraction and counts the rows left after a `DISTINCT`.

### Casts of booleans to numbers, and of lists

- `CAST(b AS INT)` and `CAST(b AS DOUBLE)` of a boolean are 1, 0 or NULL, so
  `b.cast("int64").sum()` counts the trues
  ([#1911](https://github.com/AlexanderNenninger/substrait-lean/issues/1911)).
- A list casts element by element, `transform(l, x -> CAST(x AS t))`. Polars runs it;
  the SQL engines refuse the lambda until
  [#348](https://github.com/AlexanderNenninger/substrait-lean/issues/348). A cast of a
  struct is refused by design: sverify cannot build a struct
  ([#1919](https://github.com/AlexanderNenninger/substrait-lean/issues/1919), ruling 186).

### `first(order_by=)`, `last(order_by=)` as windows and `arbitrary()`

`first(order_by=)` and `last(order_by=)` over a window ([#1913](https://github.com/AlexanderNenninger/substrait-lean/issues/1913)) are read as `FIRST_VALUE` / `LAST_VALUE` over the whole partition in that order, as Ibis writes them. `arbitrary()` ([#1920](https://github.com/AlexanderNenninger/substrait-lean/issues/1920)) is read as `first()` without an order: a non-NULL value of the group, proved as membership, reported as the engine's choice unless the group is a key.

### `group_concat` over a window, RANGE frames over `timestamptz`

`group_concat(sep=)` as a window function ([#1915](https://github.com/AlexanderNenninger/substrait-lean/issues/1915)) joins the frame's non-NULL strings in the window's order, on DuckDB. RANGE frames with interval offsets accept a timestamp with time zone as the sort key ([#1931](https://github.com/AlexanderNenninger/substrait-lean/issues/1931)).

### Quantile of a decimal: the refusal names the cast

`median()` and `quantile()` of a decimal column stay refused, by design: DuckDB truncates a double interpolation, and Spark and Polars return doubles, so no engine gives one value ([#1921](https://github.com/AlexanderNenninger/substrait-lean/issues/1921)). The message says to cast the column first (`x.cast("float64").quantile(q)`), which verifies and runs on DuckDB.

### A double cast to a timestamp is read as seconds

Sverify reads Ibis's `x.cast("timestamp")` of a double as seconds since the
epoch, as DuckDB's `to_timestamp` does: the microseconds are `x * 1e6`
computed as a double and rounded half to even, so `2.5e-6` seconds is 2
microseconds ([duckdb-to-timestamp-double](engines/duckdb/facts/duckdb-to-timestamp-double.json)).
A value outside the timestamp range raises. `try_cast` and a cast to a
timestamp with a time zone stay refused
([#1922](https://github.com/AlexanderNenninger/substrait-lean/issues/1922)).

### Dates and times: more Ibis constructs

Ibis `date_bin`/`delta` of literal timestamps (#1924), a date part such as
`iso_year` of a constant date (#1927), a date or timestamp moved by a column's
count of months or years (#1925, the day cut to the month's length, as DuckDB
does) and `ibis.timestamp(y, m, d, h, mi, s)` of integer columns (#1928, with
DuckDB's ranges for the time) are read.

### Ibis `unnest(keep_empty=True)`

An empty or NULL list gives one row with a NULL element (#1917), as DuckDB,
Polars and Spark's `explode_outer` do. `unnest(offset=)` stays refused.

### SQL lift: GROUP BY ALL, QUALIFY and strftime

`GROUP BY ALL` groups by the select items without an aggregate, `QUALIFY`
filters a window column, and `strftime(ts, fmt)` with a constant format of
`%Y %m %d %H %M %S %j %%` is read (#1991, #319). `current_date` and `now()`
stay refused, naming the function; pass the date in as a column or a constant.

### Ibis reads `truncate("ms")` and `truncate("us")`

`ts.truncate("ms")` and `ts.truncate("us")` of a timestamp are read as `date_trunc('millisecond', …)` and `date_trunc('microsecond', …)`, which Lean, DuckDB, Polars and Spark already modelled ([#1929](https://github.com/AlexanderNenninger/substrait-lean/issues/1929)). Nanoseconds stay refused. A cast of a timestamp to a number stays refused by design (DuckDB has no such cast; the replay ledgers say why); a number to a timestamp waits on the question of #1933's reading ([#1922](https://github.com/AlexanderNenninger/substrait-lean/issues/1922)).

### A literal column has its declared width

A column projected from an integer literal now has the literal's declared type's
width, not its value's: `ibis.literal(0, "int64")` starts a 64-bit column, so
adding to it is checked at 64 bits, where sverify used to report `may fail:
overflow` at 8 bits and refuse the plan. An `int8`, `int16` or `int32` literal
keeps its narrower width ([#1934](https://github.com/AlexanderNenninger/substrait-lean/issues/1934)).

### sverify-dbt reads more row-level tests

`sverify-dbt` maps the regex, LIKE, length and column-pair tests of dbt-expectations, and `not_accepted_values` and `not_empty_string` of dbt-utils, to conditions sverify proves ([#1936](https://github.com/AlexanderNenninger/substrait-lean/issues/1936)). A regex test with `flags` is listed as not checked, with the reason.

### SQL lift and plans without a table: more functions

The SQL lift reads `radians(x)` and `degrees(x)` (#1938), `right(s, n)` with a
column or expression for `n` (#1942), `str_split` inside the arguments of
another `str_split` (#1940) and a `WITH` in front of a `UNION`, `EXCEPT` or
`INTERSECT` (#1939). A plan that reads no table, as an Ibis scalar expression
makes, now runs on DuckDB (#1916); Polars refuses it, naming the construct.

Under `semantics="duckdb"`, the lifted integer `%` lists `MIN % -1` as an issue, since DuckDB raises there (#2058); a bound on either operand discharges it. DuckDB, Polars and Spark run the guard; an engine that cannot raise it refuses the plan and names it.

### sverify-dbt reads row-count and column-set tests

`expect_table_row_count_to_equal` and `expect_table_row_count_to_be_between` become a cap on the model's rows (`sv.max_rows`): proved from the upper bound in a model's tests, and a precondition when an input states it. A lower bound above 0, `group_by` and `row_condition` are refused by name. `expect_table_columns_to_match_set`, `…_match_ordered_list`, `…_contain_set`, `…_not_contain_set`, `expect_table_column_count_to_equal`, `…_be_between` and `expect_column_to_exist` are decided from the model's columns, without a proof. Tests of two relations or of a lower bound (`equal_rowcount`, `recency`, `…_distinct_count` and others) are listed as not checked, each with the reason ([#1937](https://github.com/AlexanderNenninger/substrait-lean/issues/1937)).

### Nested double arithmetic in DuckDB SQL checks in under a second

`sv.verify` of DuckDB SQL under `semantics="duckdb"` took time exponential in
how deeply double arithmetic nests: six chained divisions took 193 s
([#1952](https://github.com/AlexanderNenninger/substrait-lean/issues/1952)).
Each operation's NaN and infinity handling names its operands several times,
and the lift copied a nested operand once per mention. It now computes a
nested operand once, as a column below the `SELECT` list, wherever every row
evaluates it anyway, so the plan grows linearly: ten divisions check in about
0.6 s. The checker also keys a projection's declared column types by a short
encoding of its expressions, which makes the check of a plan 10 to 20
projections deep 13 to 20 times cheaper.

### `odcs.read` reads id paths to properties without an id

An id path such as `schema/products_obj/properties/id` names a property with no
`id` of its own by its `name`, as ODCS's example `schema/relationships.odcs.yaml`
writes it, so both foreign keys of that example read as `sv.references`. A
relationship sverify leaves unread now says why: it is not a foreign key, it
names no single column the contract defines, or it is a composite key (#2223)
(#1956).

### ODCS: patterns and object-level foreign keys

`odcs.read` reads `logicalTypeOptions.pattern` as a search condition (ODCS's patterns are unanchored) when the pattern is in the regular-expression subset all engines agree on ([#1957](https://github.com/AlexanderNenninger/substrait-lean/issues/1957)), and reads foreign keys written on the schema object and references by id path (`schema/<object id>/properties/<property id>`) as `references` ([#1956](https://github.com/AlexanderNenninger/substrait-lean/issues/1956)). A composite foreign key is listed as unread: `references` takes one column. A condition whose SQL holds braces, such as `{8}`, no longer breaks the condition query.

### Binary and map columns pass through

Sverify carries a column of a type it does not read, such as binary or a map,
through a plan unchanged on DuckDB, Polars and Spark: a `SELECT *` over a table
with a binary or map column, a filter or join on other columns, a sort on
others, `UNION ALL` and `LIMIT`. `IS NULL` and `IS NOT NULL` read such a column.
Any other use is refused, and the message names it: a function, comparison or
cast of the column, a filter, join, sort, grouping or partition on it, and
`DISTINCT` over it. A binary constant stays refused
([#1958](https://github.com/AlexanderNenninger/substrait-lean/issues/1958),
[#1918](https://github.com/AlexanderNenninger/substrait-lean/issues/1918)).

### A CASE of constants has its declared width

A column computed by a `CASE` whose branches are integer constants now has the
width their declared type gives, as a literal column does since
[#1934](https://github.com/AlexanderNenninger/substrait-lean/issues/1934):
`CASE WHEN x > 0 THEN 100 ELSE 0 END` of `BIGINT` literals is a 64-bit column, and
`e * e` of it is no longer reported as an 8-bit overflow. A `CASE` of `TINYINT`
constants stays 8 bits ([#1968](https://github.com/AlexanderNenninger/substrait-lean/issues/1968)).

### Six more DuckDB rows are proved

DuckDB's `division_type`, `round`'s rounding, NaN equality, `substring`'s
negative start, `LIKE`'s case sensitivity and string positions are now
proved by the generated lowering (`Lowering.duckdb_exact`), so a plan that
reads them no longer lists them as tested rows
([#1985](https://github.com/AlexanderNenninger/substrait-lean/issues/1985)).
DuckDB's integer powers are named as a shim, written as checked products.

### `sv.asof_join(how="left")` keeps every left row, proved

Sverify now proves that a left as-of join has one output row per left row:
every result the reference allows has as many rows as the left table
(`AsofSite.left_exactly_one`,
[#1992](https://github.com/AlexanderNenninger/substrait-lean/issues/1992)).
The checker's as-of sites report whether a plan has the shape the theorem is
about (`left_exact`).

### A left key survives `sv.asof_join`

A key of the left table that `requires` states is now proved a key of
`sv.asof_join`'s output, for `how="left"` and `how="inner"`: `unique(order_id)`
on the facts gives `unique(order_id)` after the join
([#1992](https://github.com/AlexanderNenninger/substrait-lean/issues/1992)).
The key analysis keeps a dependency through a projection's copies of the
columns it depends on, which helps any plan that renames or reorders columns
above a join.

### A key survives a GROUP BY of the key and its attributes

`unique(customer_id)` on the input now proves `unique(customer_id)` after `GROUP BY customer_id, name`, and after the same grouping of `customers LEFT JOIN orders`. Sverify carries functional dependencies through the plan (a key gives every column, and a join's left side keeps its dependencies), and a dependency onto a key makes its left side a key ([#1993](https://github.com/AlexanderNenninger/substrait-lean/issues/1993)).

### sverify-dbt suggest names the input test that proves a model test

`sverify-dbt suggest` tries `not_null` on the seed and source columns no test covers when a model test fails because a row may fail it, and names the minimal set that proves the test, such as `not_null` on `raw_orders.ordered_at` for `fct_daily_revenue.not_null(order_day)`. It used to print that nothing more was provable ([#1994](https://github.com/AlexanderNenninger/substrait-lean/issues/1994)).

### sverify-dbt fails a refused model with an enforced contract

`sverify-dbt check` exits 1 under the default `--fail-on contract` when sverify refuses a model whose contract is enforced, and names the refusal on stderr; it used to exit 0 on exactly the model it could not read ([#1995](https://github.com/AlexanderNenninger/substrait-lean/issues/1995)). A refused model without a contract still exits 0.

### Pipelines ignore an unused map, struct or binary column

A pipeline over a table with a map, struct or binary column no step mentions refreshes, as `verify` does, with or without `requires`. The plans of the view's strategies (delta rules, state per group, touched groups, semi joins) read the columns the view and its conditions mention (#1996).

### Clearer first hour: run-time checks, constants, quarantine, refresh summary

- A report that holds with checks reads "proved with checks: 1 run-time check" (it said "1 assumption"), matching the `while it runs:` lines below it.
- Double constants print as Python writes them: `amount * 3.0 + 1.0`, not `amount * 3.000000 + 1.000000`, and `value * 3.0000001` keeps its digits.
- `sverify check`'s "Not proved" lines say each postcondition in words (`total < 5: it may be FALSE on some rows`), as its guarantees do.
- `sverify check` lists a node's quarantine table among its credentials only where a precondition sets rows aside (`on_violation="quarantine"`).
- `Refresh.summary()` is one line per node for every refresh: a first refresh reads "paid: computed, requires checked on data, created v1: +2 −0", and what is notable (a recompute, a schema change) leads the line; `str()` keeps the full entry.

([#1997](https://github.com/AlexanderNenninger/substrait-lean/issues/1997))

### Install lines lead with the engine, and a refused run names its postcondition in words

- The install sections of `python/README.md`, `docs/getting-started.md`, `docs/engines.md` and the `sverify` skill lead with `pip install 'sverify[duckdb]'`, which the first example needs; `pip install sverify` follows as the verify-only install.
- `UnverifiedRunError` and the unverified-refresh warning say `ensures total < 5 is not proved`, as `sverify check` does, with the Python syntax left out.

([#1997](https://github.com/AlexanderNenninger/substrait-lean/issues/1997))

### A rewrite no longer runs where the plan as written may raise

`Report.run` could run a proved rewrite that dropped the part of the plan
that raises, such as a left join's unused input whose `SUM` may overflow, and
return rows where the reference raises
([#2006](https://github.com/AlexanderNenninger/substrait-lean/issues/2006)).
The rewrite now runs only where neither the plan as written nor the rewrite
has an issue; otherwise the engine runs the plan as written, and `run_gate`
says `issues`.

### The default semantics' SQL lift is proved against DuckDB

SQL lifted under `semantics="reference"` now uses the proved entries of the
lift's reference table, and Sverify proves that each of them, wherever it gives
a value, gives DuckDB's (`liftReference_refines_duckdb`, D54,
[#2008](https://github.com/AlexanderNenninger/substrait-lean/issues/2008)).
`CAST(DOUBLE AS BIGINT)` stays refused under the reference (D55), now with the
refusal text of the Lean table.

### Wordings that match their theorems

The PyPI page, `Verdict.PROVED`, `ViewContract.deterministic` and `verify`'s `semantics` docstring say what the theorems state: the proof holds for the model of each engine's functions, and that the model matches the engine rests on tests ([#2009](https://github.com/AlexanderNenninger/substrait-lean/issues/2009)).

### A decimal average over a window stays within its inputs

`AVG` of a decimal column over a window now keeps the bounds of the values it averages, as a grouped `AVG` already did. A sum minus its average per partition, or a ratio that divides by that average, no longer reports an overflow or a division by zero that its inputs' bounds rule out ([#2015](https://github.com/AlexanderNenninger/substrait-lean/issues/2015)).

### Assumed issues are checked by a plan whose result is the verdict

A report's assumed issues (an integer `SUM` that must fit 64 bits, an
operation on finite doubles that must not give `±∞`) were checked by guards
inside the plan an engine runs. DuckDB and Spark skip an expression the result
does not need: a column nothing reads, one under a filter or a limit pushed
below it, one joined to an empty input, one under a `count(*)`. There a run
returned rows where the reference raises
([#2018](https://github.com/AlexanderNenninger/substrait-lean/issues/2018)).
`Report.run` now first runs a check plan the checker writes from the plan as
written (`assumed_check` in the report's JSON), on the run's own engine: one
row, one column per place where an issue may occur, aggregates every engine
computes. A batch on which an issue occurs is refused with a
`PreconditionError` before the run. The guards inside the plan stay. The
DuckDB run of the whole plan before another engine's run is gone, and so is
`ProfilePlugin.checks_assumed` and `check_inputs`'s `assumed_checked`.

### Spark names a parser refusal

When Spark's parser refuses the SQL sverify wrote for a plan as too complex (a nest of about 80 levels), the run raises `UnsupportedError` with the statement's size and the fact `spark-exec-parser-depth` in place of Spark's `FAILED_TO_PARSE_TOO_COMPLEX` error
([#2030](https://github.com/AlexanderNenninger/substrait-lean/issues/2030)).

### DuckDB 2.0.1 is probed

DuckDB 2.0.1 joins 2.0.0 as a probed version of the DuckDB table (`alsoProbed`). The sqllogictests that changed between the tags were replayed at 2.0.1: the disagreements each cite an engine fact or an open issue ([#2045](https://github.com/AlexanderNenninger/substrait-lean/issues/2045), [#2376](https://github.com/AlexanderNenninger/substrait-lean/issues/2376)).

### Engine versions: one range per profile

Each engine profile now covers one range of engine versions: the minor releases its facts were probed at (D70, amending D14). The engine packages depend on that range, `duckdb>=2.0.0,<2.1`, `polars>=2.1.0,<2.2` and `pyspark>=4.3.0,<4.4`, and sverify-dbt's DuckDB bound is the same; a test holds each bound to its profile. A run on an unprobed patch inside the range warns (`EngineVersionWarning`) and records the version on its route as `Route.unprobed_version`, also in the report JSON, and the route's evidence line says "this run is on 2.0.1, unprobed". A run on another minor is refused (`EngineVersionError`, which names the range); before, only another major was. `run(..., unverified=True)` now also runs a proved plan on a refused version, unverified. A Spark session's own version decides. `warnings.simplefilter("error", sverify.errors.EngineVersionWarning)` refuses every unprobed version ([#2052](https://github.com/AlexanderNenninger/substrait-lean/issues/2052)).

### What an unproved run does where the reference raises

The docs say it: an unproved run does what its engine's facts record at the probed version, and no theorem covers it. The integer-overflow row of the pitfalls table names the versions and links the facts ([#2054](https://github.com/AlexanderNenninger/substrait-lean/issues/2054)).

### A double sum under `semantics="duckdb"` keeps its overflow check

Under `semantics="duckdb"`, a `sum` or `avg` of doubles no longer drops the overflow to `±∞` from its issues: DuckDB's running sum overflows where the model's exact sum stays finite (`avg(1e308, 1e308)` is `inf` in DuckDB), so a verification over an unbounded double column is `proved_with_checks` where it was `proved`, and a run refuses a batch that overflows. A scalar operation's `±∞` stays the engine's value there. The check also tests the total for NaN where no input is NaN: partial sums that overflow in both directions combine to NaN ([#2057](https://github.com/AlexanderNenninger/substrait-lean/issues/2057)).

### The catalogue's prose names where the facts are

`catalogue/` points to `engines/<engine>/facts/` for the engine facts, and its feature notes no longer present DataFusion as a current engine ([#2081](https://github.com/AlexanderNenninger/substrait-lean/issues/2081)).

### `sverify contract export` drops `--format`

`sverify contract export` writes ODCS, its one format, so its `--format odcs` flag is gone: drop it from the command. The flag chose nothing, and the 1.x promise keeps a flag for good once 1.0 ships ([#2081](https://github.com/AlexanderNenninger/substrait-lean/issues/2081)).

### The refusal of a duration compared with an interval of days or months gives its own reason

A comparison of a duration (`ts - ts`, `d - d`) with an interval of days or months is still refused, and the message now says why: durations compare as microseconds, and no month length suits every engine. Write the interval in hours or seconds ([#2081](https://github.com/AlexanderNenninger/substrait-lean/issues/2081)).

### `power` is strict in a NULL base

`power(x, 0)` is NULL for a NULL `x`, as DuckDB, Polars and Spark give it. It was the constant 1: the parser, the SQL plan reader and the Polars engine folded a literal zero exponent, and the base was never evaluated. A proof that `power(x, 0)` is not NULL now needs `x` not NULL. For a non-NULL `x` the result is still 1, NaN and `±inf` included. On Spark, a double `power(x, 0.0)` is refused with the other double powers ([D71](docs/decisions.md#d71-power-is-strict-in-both-arguments), part of [#2081](https://github.com/AlexanderNenninger/substrait-lean/issues/2081)). Every incremental sink is recomputed once at the upgrade, since a stored plan keeps `power(x, 0)` and the stored 1 is no longer the reference's value.

### A typed NULL beside a nested call keeps its type in the written plan

`CAST(NULL AS DOUBLE)` projected beside a nested call such as `-(d + d)` was written as an `i64` NULL, so Polars returned an `int64` column and DuckDB an untyped one. The written plan now keeps the declared type (#2102).

### A condition of `NOT NULL` takes the ELSE branch in the written SQL

A `CASE WHEN NOT CAST(NULL AS BOOLEAN) THEN a ELSE b END` in a written plan took the THEN branch, because the writer folded `NOT NULL` to `TRUE`. `NOT NULL` is NULL, and the CASE takes ELSE, as the reference and the engines' own SQL do.

### A stated float tolerance keeps the plan as written

Under `sv.equivalent(floats=sv.within(...))`, an engine now runs the plan as written in place of the checker's rewrite, as it already did under `floats="plan"`. The exception is a plan where the rewrite is proved safe at every engine's doubles: one with no double and no open measure. The report names the gate (`run_gate` is `"near"`) ([#2105](https://github.com/AlexanderNenninger/substrait-lean/issues/2105)).

### The SQL lift refuses `lpad` and `rpad` past 2^20 characters

`lpad(s, n, p)` and `rpad(s, n, p)` with a constant `n` over 1,048,576 characters are refused, with the reason. The lift writes the fill as a constant of `n` characters, and `lpad('', 1100000000, '😀')` built 4.4 GB of it before DuckDB refused the query at its string limit ([#2135](https://github.com/AlexanderNenninger/substrait-lean/issues/2135)).

### A FLOAT cast to an integer in DuckDB SQL is refused

A DuckDB SQL `CAST(x AS INTEGER)` of a `FLOAT` (REAL) is refused as the cast
of a `DOUBLE` is: DuckDB rounds it to the nearest integer, and the model's cast
truncates. Sverify used to prove the truncated value, 0 for `0.55::FLOAT`
where DuckDB gives 1. The message names spellings that lift, with
`CAST(x AS DOUBLE)` in place of the `FLOAT`
([#2152](https://github.com/AlexanderNenninger/substrait-lean/issues/2152)).

### SQL lift: `MEDIAN` of a date, timestamp or FLOAT is refused

DuckDB interpolates the median of a date, timestamp or FLOAT (`2024-01-05 12:00:00` for the days 1 to 10) where the lift took the lower middle, a different value ([#2153](https://github.com/AlexanderNenninger/substrait-lean/issues/2153)). The lift now refuses it and names the rewrite: `quantile_disc(x, 0.5)` for the lower middle, or a cast to DOUBLE.

### `signbit` at zero, and black-box refusals in a long-lived checker

Lean now evaluates DuckDB's `signbit` at `+0.0` and `-0.0` (FALSE and TRUE), and refuses it at NaN only. A call Lean does not evaluate (`signbit` of NaN, `string_split('', '')`) is refused every time. Before, the second such call in one checker process read NULL and was reported as a broken law ([#2154](https://github.com/AlexanderNenninger/substrait-lean/issues/2154)).

### `drop_null` of no column verifies

An Ibis `drop_null([])` (an empty subset, or a table with no column to test) no longer crashes the producer with an `IndexError` ([#2155](https://github.com/AlexanderNenninger/substrait-lean/issues/2155)). With `how="any"` every row stays; with `how="all"` none does, as DuckDB gives.

### Fixed

- The SQL writer no longer refuses `corr` and `cov` of booleans (`(t.G > 34.0).corr(t.G <= 34.0)`) after the checker accepted them: it read `abs` of a double built from an `IF` as an integer `abs`, as Lean's parser does not ([#2158](https://github.com/AlexanderNenninger/substrait-lean/issues/2158)).

### Written list_sum raises sverify's tagged check

`list_sum` past 64 bits now raises sverify's own tagged check ("list_sum out of range") in the written SQL, instead of DuckDB's untagged cast error. The report and the semantics are unchanged (#2162).

### The report lists an ordering comparison of lists

A DuckDB SQL query that orders lists (`<`, `<=`, `>`, `>=`, `BETWEEN`, `greatest`, `least`) now shows a dialect difference, `list_null_order`, in `Report.dialect_differences`, under every semantics. Where a NULL element decides the order, the plan gives NULL and DuckDB orders the NULL last: `[1,2] < [1,NULL,3]` is NULL here and TRUE on DuckDB (part of [#2163](https://github.com/AlexanderNenninger/substrait-lean/issues/2163)). The verdict is unchanged.

### SQL lift: a CTE named like an input no longer hides the input's qualified name

With an input keyed `main.orders`, `WITH orders AS (SELECT ... FROM orders) SELECT ... FROM orders` was refused as an unknown table: the lift skipped every table named like a CTE anywhere in the query. It now skips only the names a CTE has in scope, so the CTE's body reads the input ([#2169](https://github.com/AlexanderNenninger/substrait-lean/issues/2169)). A CTE named like its own source table already lifts since [#2166](https://github.com/AlexanderNenninger/substrait-lean/issues/2166)'s fix.

### A sorted result is sorted once

Under a multiset observation, the SQL Sverify writes for a result that ends in a sort, or a top-N, sorts by the sort's own keys. It no longer numbers the rows by those keys and sorts again by the number. Spark and Snowflake write this by default, and DuckDB's checked runs do where the order of ties can't be observed (#2186).

### A CASE over doubles on Polars runs in the memory of its input

A `CASE` around ordering comparisons of doubles took 5 to 6 GB on Polars for a 64-row table: the plan Polars collects has no common-subexpression elimination, and the lowering wrote a nested operand six times per comparison and listed an operand's issues once per read. Each operand is written once and each distinct issue is checked once; the same plan peaks near 500 MB
([#2210](https://github.com/AlexanderNenninger/substrait-lean/issues/2210)).

### `substrait-check --help`

The Lean checker prints a usage page for `--help` and `-h`: its flags grouped
(checking a plan, diagnostics, serving, tables and coverage), one line each,
with an example and the exit codes. An unknown flag, a flag used without its
file and a file it can't read are usage errors with one line on stderr and
exit 2, where they ended in an uncaught exception before
([#2239](https://github.com/AlexanderNenninger/substrait-lean/issues/2239)).
The flags keep their names.

### `repeat('', n)` returns at once

The checker returns `''` for `repeat('', n)` without counting to `n`, so a plan that repeats an empty string `2^63 - 1` times no longer hangs it ([#2278](https://github.com/AlexanderNenninger/substrait-lean/issues/2278)).

### A `file:` URI on another host is no local path outside Windows

On Linux and macOS, `file://otherhost/x` was read as the local file `/x`. Such a URI now takes the non-native read path. On Windows the host is a UNC share as before, and `file:///x` and `file://localhost/x` read as before ([#183](https://github.com/AlexanderNenninger/substrait-lean/issues/183), [#2306](https://github.com/AlexanderNenninger/substrait-lean/pull/2306)).

### A cast to a type that holds a struct is refused

A cast whose target is a struct, or a list of structs, is refused: the model carries no field names, so a target with the same field kinds in another order read as the identity, where DuckDB and Polars pair a struct cast's fields by name and Spark by position. The proper pairing follows ([#2376](https://github.com/AlexanderNenninger/substrait-lean/issues/2376)).

### Polars's double sums are proved, as the streaming engine adds them

Polars's profile states its double `SUM` and `AVG` as the streaming engine
computes them, sequential per group and pairwise per morsel
(`polars-sum-float-streaming`). Kahan's compensated sum is the in-memory
engine's, which sverify refuses, and it left the profile
([#2411](https://github.com/AlexanderNenninger/substrait-lean/issues/2411)).
A postcondition that holds on the reference's sum and keeps its sign is now
proved on Polars, as on DuckDB and Spark, where it was tested: five catalogue
queries (clickbench q09, q13, q37 and q42, and h2o-groupby q1) run on Polars
with proved evidence.

### `sverify-dbt` reads past a column list that names no columns

A `unique_combination_of_columns` test whose `combination_of_columns` holds a null, or is a bare string, made `sverify-dbt check` fail with a `TypeError` for the whole project. Such a test is now not checked, with the reason "its columns are no list of column names", and the project's other tests are checked as before. dbt itself fails such a test ([#2414](https://github.com/AlexanderNenninger/substrait-lean/issues/2414)).

### A Flight source refuses a log that restarted

A `FlightLog` that restarted numbers its batches from 1 again, and a `FlightSource` took it for the log its cursor was read from and skipped every new batch numbered up to the cursor. The log now has an identity (`FlightLog.id`, the `log` key of the stream's schema metadata), the cursor records it, and `read`, `restore` and the audit raise an error naming both logs when they differ; reading the log again is your choice, by starting the node on a new sink. Cursors recorded before this release name no log, so existing Flight cursors refuse once after the upgrade: a job with an old sink and a `FlightLog` server sees the error, and starts the node on a new sink to read the log again. `FlightLog` gains the public `id`; a Flight server of another make that names no log is read as before ([#2426](https://github.com/AlexanderNenninger/substrait-lean/issues/2426)).

### Secrets and Flight: values read as written, errors that say what is wrong

- A `KEY=value` secret file loses only one pair of matching quotes around a value, so `PASSWORD=abc'` reads as `abc'` ([#2429](https://github.com/AlexanderNenninger/substrait-lean/issues/2429)).
- A JSON field that is not a string reads as its JSON: `true`, `null`, `{"a": 1}`. This applies to `file:` secrets and to OpenBao and Vault ([#2429](https://github.com/AlexanderNenninger/substrait-lean/issues/2429)).
- `azure-kv:` takes a vault's URL as well as its name, as in `azure-kv:https://myvault.vault.azure.net/lake` ([#2433](https://github.com/AlexanderNenninger/substrait-lean/issues/2433)).
- A misconfigured secrets backend says what is wrong, such as `[secrets.bao]: unexpected keyword argument 'adress'`, and a `names` table without `ref` says so ([#2428](https://github.com/AlexanderNenninger/substrait-lean/issues/2428)).
- `FlightLog` refuses a ticket whose values have the wrong type with the ticket's shape, and no longer answers with a server traceback ([#2427](https://github.com/AlexanderNenninger/substrait-lean/issues/2427)).

### A double→integer cast in `to_substrait` now carries ST-6's shim or assumption

Substrait leaves open how a cast of a double or a decimal to an integer rounds ([ST-6](upstream/bugs/ST-6.json)), and `to_substrait` exported such a cast as exact. The cast now reads `float_to_int`: `shims="apply"` truncates first (`floor` for `x >= 0`, `ceil` otherwise, then the cast), `"annotate"` ships ST-6's assumption, and `"refuse"` refuses. Under `semantics="substrait"` such a plan is no longer proved ([#2438](https://github.com/AlexanderNenninger/substrait-lean/issues/2438)).

### `try_cast` of a double to an integer is proved again on every engine

Each engine's table now states its double or decimal to integer cast
(`float_to_int` at `cast.num`, ruling 273): Polars and Spark truncate natively,
and DuckDB's cast rounds, so its lowering writes `trunc` first, a shim. The
route of `try_cast` goes back from tested to proved on DuckDB, Polars and Spark
([#2438](https://github.com/AlexanderNenninger/substrait-lean/issues/2438)).

### `to_substrait` exports `min` and `max` of values that are not lists

The default `to_substrait()` refused every `min` and `max`, even of an integer column, naming `list_null_order`: where a NULL element sorts inside a list. That option now matters only where a value of the plan may be a list, so `min` and `max` of integers, doubles and strings export, and of lists still depend on it ([#2439](https://github.com/AlexanderNenninger/substrait-lean/issues/2439)).

### A sink refuses a commit over a state read from another source

Two nodes that shared a sink and an `app_id` could read different sources under one name, and a source with no table id (a Flight source) left only its versions to tell them apart: the second writer skipped or replaced the other's rows without a word. The contract now records what identifies such a source (`fingerprints`, an optional key of the sink's contract record; a Flight source's is its server and table), and a commit over a state with another fingerprint raises an error naming both sources. A record written before this release has none and is not compared ([#2441](https://github.com/AlexanderNenninger/substrait-lean/issues/2441)).

### OpenLineage: `read` takes a file holding one event over several lines

`sverify.openlineage.read` reads a JSON file holding one event written over several lines, as `jq .` or Marquez's UI save it. It used to fail with a `JSONDecodeError` ([#2447](https://github.com/AlexanderNenninger/substrait-lean/issues/2447)).

### `Upstream.schema` reads Spark's nested types as Spark means them

A `schema` facet's `struct<…>`, `array<…>` and `map<…>` now read Spark's type names inside them as Spark's, so `struct<a:int>` is `struct<a: int32>` and `timestamp` inside a struct is `timestamp('UTC')`, the types the Spark job wrote. A malformed nested type is `unknown`. Recent type names are cached ([#2448](https://github.com/AlexanderNenninger/substrait-lean/issues/2448)).

### `strpos` and `contains` on long strings run in linear time

The checker searched a string for a needle by testing every position, up to `n · m` comparisons. A long, almost-matching needle took DuckDB's `test_contains_long_almost_matching_needle` past the replay's 120 s watchdog. The search now rolls a hash over the string and compares characters only where the hash matches, proved equal to the reference's search (`Text.Find.findFrom_eq_fast`). That replay file takes 6 s, and `strpos`, `contains`, `instr` and `position` on long strings stop being quadratic in `verify` (#2497).

### The replay skips queries DuckDB's time limit interrupts

The DuckDB replay (`sverify_dev.slt`) skips a query that DuckDB stops with `max_execution_time` ("Query exceeded maximum execution time"): the time limit is an outcome no model states. `function/string/test_levenshtein_interrupt.test` no longer runs Lean into the checker's watchdog, and queries that finish under the limit are replayed as before ([#2498](https://github.com/AlexanderNenninger/substrait-lean/issues/2498)).

### Polars refuses a variance beside a list in one grouping

On Polars, a grouping that holds a list-computed measure (`ARRAY_AGG` and the
like) runs on the in-memory engine. Its `VAR_*` and `STDDEV_*` then use the
in-memory algorithm, not the one the Polars profile states and proves the
bound for. The translation to Polars now refuses such a grouping, as it does
for a double `SUM` or `AVG`
([#2507](https://github.com/AlexanderNenninger/substrait-lean/issues/2507)).
The plan still runs on the other engines. On Polars, compute the list and
the statistic in separate groupings.

### A LEFT JOIN on a declared foreign key keeps the right side's non-NULLs

Where `sv.references` (or a dbt `relationships` test, which sverify-dbt reads as one) says every left row of a `LEFT JOIN` has a match, the proofs read the join as an inner join: the columns of the right side are as non-NULL as they are on their own, for example a `SUM` over a group of a non-NULL column. The report names the step ("left join on a foreign key, under references …"); without the reference, the column stays unproved and the report proposes `sv.references`. The plan that runs stays the LEFT JOIN. On jaffle_shop with the declared relationship, the five `orders` amount tests are proved: 19 of the project's 20 tests, up from 14 ([#2512](https://github.com/AlexanderNenninger/substrait-lean/issues/2512)).

### A cast of a double to a decimal reads `decimal_rescale`, and `to_substrait` carries ST-8's assumption or refuses

Substrait leaves open both which value a cast of a double to a decimal rounds and how ([ST-8](upstream/bugs/ST-8.json)): DuckDB and Polars round the double product `x · 10^s`, half away from zero and half to even, and Spark's native cast rounds the double's shortest decimal text (`1.005` to `DECIMAL(3,2)` is 1.01 there). The cast now reads `decimal_rescale`, and Polars's and Spark's profiles state their own casts, so the generated lowerings no longer write the native cast on those engines. `to_substrait` with `shims="apply"` refuses such a cast, `"annotate"` ships the assumption that the consumer rounds the double product half away from zero, and `"refuse"` refuses ([#2523](https://github.com/AlexanderNenninger/substrait-lean/issues/2523)). The values sverify writes and runs are unchanged.

### Refusals name the open issue

A refusal of a function that Polars's or Spark's writer does not run yet now
names [#2540](https://github.com/AlexanderNenninger/substrait-lean/issues/2540),
the open issue for that work, where it named #271, which is closed. Snowflake's
refusals say that its profile is out of tree. Every such refusal still ends with
its exit, `run it with engine='duckdb'`.

### `exp`, `sqrt` and the trigonometric functions route to Spark

`pow_one_inf` belongs to `power` alone (D40), but sat on the group of every elementary function, so Spark's refusal of it refused `sqrt`, `exp`, `sin` and the rest. The group `fp.elem` is split into `fp.pow` (`power`), `fp.atan2` (`atan2`) and `fp.elem` (the unary functions) (ruling 163). `sqrt`, `exp`, `sin`, `cos`, `tan`, `asin`, `acos` and `atan` of doubles now route to Spark with the bounds of [#1818](https://github.com/AlexanderNenninger/substrait-lean/pull/1818); `power` and `atan2` stay refused there, each naming its own group. Reports for plans with a unary function no longer list `pow_one_inf` among their options, on any engine. No reference value or allowed set changes.

### Polars's lowering is generated and proved

Polars now has a generated lowering, as DuckDB has: each function Polars
computes its own way gets a template, proved to give the reference's value
under Polars's profile (`Lowering.polars_exact`,
[#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)).
Integer `//` and `%` truncate from Polars's floored ones, `round` and `ceil`
give `0.0` for a negative value that rounds to zero, and `%` of doubles is
refused. Polars's `rounding`, `pow_one_inf`, `negative_start` and
`case_sensitivity` rows, and DuckDB's `round_zero_sign` and `pow_one_inf`
rows, are now proved. `Profile.polars`, which `semantics="polars"` will
verify under, states Polars's `-0.0` from `round` and `ceil`. The translation
to Polars still writes these functions by hand, and a test checks that it
agrees with the table.

### Polars runs its generated lowering

The translation to Polars now writes integer `//` and `%`, `round` and `ceil`
from the generated lowering table (`sverify_polars.lowering`), the templates
`Lowering.polars_exact` proves
([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)). The
hand-written shims `int_div_trunc` and `int_mod_trunc` are gone. `round` and
`ceil` of a negative value that rounds to zero now give `0.0` on Polars, as the
reference does, where they gave `-0.0`; the two are one value for every
comparison sverify makes. Polars's `division_type` and `round_zero_sign` rows
are proved by `Lowering.polars_exact`.

### Spark runs lists

Spark now runs `unnest()`, list literals, list elements and lengths, and an unordered `collect()`
([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)): `posexplode` in a lateral
subquery, `array`, `try_element_at`, `cardinality` and `collect_list`, which gives NULL where the
reference does for no values. An ordered `collect()` stays refused, since `collect_list` has no
`ORDER BY`.

### Spark runs its generated lowering

The translation to Spark writes double arithmetic, the elementary functions,
`floor`, `ceil`, `date_add` and the shifts from Spark's generated lowering
table, whose templates Lean proves
([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)).
The hand-written model of what the writer computes (`Profile.sparkWritten`) is
gone. Spark's soundness now holds on the plan the table lowers, in two
branches: with its guards dropped for a plan without IEEE division, and with
every guard kept where Spark does not raise. More Spark routes are proved
where they were tested, among them integer division, `mod`, the string
matches and the date parts, and 15 rows of Spark's table cite a theorem where
they tracked #271.

### Spark runs the logarithms of doubles

Spark now runs `ln`, `log10`, `log2` and `log(b, x)` of doubles natively ([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)).
Its values are Java's, within 1 ulp of the exact result by its source
(spark-ulp-libm), and the plan's float bound adds each function's distance
from libm's value per call. `exp`, `sin`, `cos`, `tan`, `asin`, `acos` and `atan` have their bounds
and writer too, but `sverify.verify` still refuses them on Spark, as it does `sqrt`: their group
reads `pow_one_inf`, which Spark refuses. `sin`, `cos` and `tan` are bounded up to 2²⁰. `power` and
`atan2` stay refused. The bounds of Polars's `log10`, `log2` and `log(b, x)` and DuckDB's
`log(b, x)` are restated as the sum of both distances, so they are wider.

### A decimal cast to a smaller scale in `to_substrait` now carries ST-8's assumption or refuses

Substrait leaves open how a cast of a decimal to a smaller scale rounds ([ST-8](upstream/bugs/ST-8.json)), and `to_substrait` exported such a cast as exact in every mode. The cast now reads `decimal_rescale`: `shims="apply"` refuses it, since ST-8 has no rewrite, `"annotate"` ships ST-8's assumption, and `"refuse"` refuses ([#2504](https://github.com/AlexanderNenninger/substrait-lean/issues/2504)). A plan whose decimals keep every digit (sums, products, casts to a larger scale) exports as before.

### A `MIN` or `MAX` of doubles in `to_substrait` is no longer reported as shimmed

ST-4's shim rewrites comparisons, grouping keys and sort keys of doubles, and no aggregate, yet `shims="apply"` reported a `MIN`, `MAX` or quantile of doubles as shimmed: a consumer whose `MAX` skips NaN gave another value. `"apply"` now refuses such a plan, `"annotate"` ships ST-4's assumption, and `"refuse"` refuses ([ST-4](upstream/bugs/ST-4.json), [#2505](https://github.com/AlexanderNenninger/substrait-lean/issues/2505)).

### SQL lift: named `WINDOW`, `any_value` and `DATE ± INTEGER`

The DuckDB SQL lift reads `WINDOW w AS (…)` with `OVER w` and `OVER (w ORDER BY …)`, `any_value(x)` (a non-NULL value of the group, reported as the engine's choice) and `DATE ± <integer constant>` (a DATE). `arg_min_null`, `bitstring_agg` and `histogram_exact` are refused with the reason and [#326](https://github.com/AlexanderNenninger/substrait-lean/issues/326); `DATE ± <integer column>` and `DISTINCT ON` stay refused with their rewrite ([#319](https://github.com/AlexanderNenninger/substrait-lean/issues/319)).

### `range` and `generate_series` as inputs, and built-in schema names

`FROM range(a, b[, step])`, `generate_series(…)` and `UNNEST(generate_series(…))` with constant integer, date or timestamp bounds are lifted as the rows they list (at most 10,000), so a date spine verifies (#321). A call qualified by its built-in schema (`main.lower(x)`, `pg_catalog.lower(x)`) reads as the bare function (#328).

### Refused: a sample of a series, and a percent limit

`TABLESAMPLE` on `range()` or `generate_series()` is refused. `LIMIT n PERCENT` and `LIMIT … WITH TIES` are refused on every source, tables included: the lift read a percent limit as a row count, a wrong result that tables accepted until now (#321).

### `CAST(decimal AS integer)` and scale-reducing decimal casts in DuckDB SQL

The SQL lift reads `CAST(dec AS BIGINT)` as DuckDB does, rounding half away from zero (the rescale to scale 0, then the exact cast), under `semantics="reference"` and `"duckdb"`. `CAST(dec AS DECIMAL(p, s))` to a smaller scale lifts too. The double case stays refused until the rounding cast lands (#322).

### The SQL lift reads `CAST(double AS BIGINT)` as DuckDB's rounding

`sv.verify` of DuckDB SQL lifts `CAST(x AS BIGINT)` of a double, under both `semantics`, as the cast of the half-to-even round, which is what DuckDB computes ([#322](https://github.com/AlexanderNenninger/substrait-lean/issues/322), D55). A plan's `round(x, rounding: TIE_TO_EVEN)` at zero digits is read and written on DuckDB, Polars and Spark. Casts of a double to narrower integers stay refused, with the spelling that lifts.

### Second and millisecond timestamps

Columns of `timestamp(0)` and `timestamp(3)` (Arrow `timestamp[s]` and `timestamp[ms]`) are now read as microseconds, exactly (D61, [#323](https://github.com/AlexanderNenninger/substrait-lean/issues/323)). Results are `timestamp(6)`. A cast to `timestamp(0)` or `timestamp(3)` floors on the timeline, as `date_trunc` does.

### Nanosecond timestamp columns are read

A `timestamp[ns]` column, the unit Parquet and pandas often carry, is read
with every digit on DuckDB and Polars. Sverify compares it with other
nanosecond timestamps, orders, groups and joins on it, counts it and takes its
`MIN` and `MAX`. Nanoseconds reach 1677-09-21 to 2262-04-11. A calendar
function, interval arithmetic, a cast, or a microsecond timestamp or literal in
the same comparison is refused, and the message says so. Spark holds
microseconds only and refuses the column
([#323](https://github.com/AlexanderNenninger/substrait-lean/issues/323)).

### The SQL lift reads `list_append`, `list_prepend`, `flatten`, `list_first` and `list_last`

DuckDB SQL with `list_append(l, x)`, `list_prepend(x, l)` (and their `array_` names), `flatten(l)`, `list_first(l)` and `list_last(l)` lifts (part of [#327](https://github.com/AlexanderNenninger/substrait-lean/issues/327)). A NULL list is empty for an append and a prepend and a NULL value is an element, as in DuckDB; `list_first` and `list_last` are NULL for an empty or NULL list.

### The SQL lift refuses what DuckDB refuses for `if` and `iff`

DuckDB SQL with a two-argument `if(condition, value)` is refused, as DuckDB's binder does; the lift had read it as a `CASE` without `ELSE` (part of [#328](https://github.com/AlexanderNenninger/substrait-lean/issues/328)). `iff`, which DuckDB 2.0 does not have, stays refused as an unknown function. Tests check `if` (also schema-qualified) and `arbitrary` against DuckDB.

### The SQL lift reads `ascii`, `levenshtein`, `if` and `arbitrary`

DuckDB SQL with `ascii(s)`, `levenshtein(s, t)`, `if(c, a, b)` and `arbitrary(x)` lifts (part of [#328](https://github.com/AlexanderNenninger/substrait-lean/issues/328)). `ascii` and `levenshtein` are the model's functions, which agree with DuckDB on ASCII text and raise on other text as the reference does (D43). `if(c, a, b)` is the `CASE` it abbreviates, and `arbitrary` is DuckDB's other name of `first`.

### The SQL lift reads a qualified call as DuckDB does

The lift reads `main.lower(x)` and `system.main.lower(x)` as `lower(x)`, as
DuckDB does, and refuses `pg_catalog.lower(x)`, `memory.main.lower(x)` and
`system.pg_catalog.lower(x)`, which DuckDB refuses with a binder error. `len`
and `substr` lift as `length` and `substring`, tested against DuckDB (#328).

### DuckDB's SUM and AVG of doubles with both infinities are no domain error

Under `semantics="duckdb"`, a `SUM` or `AVG` of doubles holding `+∞` and `-∞`
is NaN, as DuckDB computes it, and `verify` no longer reports a domain error
for it ([#341](https://github.com/AlexanderNenninger/substrait-lean/issues/341)).
The generated lift writes the aggregate as a sum that never sees `+∞` or NaN
and the largest and smallest value, finished by a `CASE` that gives NaN or
`+∞` where they say so; Lean proves it equals `SUM` or `AVG` of the values,
and that none of its measures has a domain error. Under the reference semantics the
aggregate and its domain error are unchanged. The written SQL has three
aggregates where DuckDB's has one, until the generated lowering folds the
pattern back (#271).

### The margin check reads DuckDB's finish of `SUM` and `AVG`

Under `semantics="duckdb"`, a threshold on a double `SUM` or `AVG` that DuckDB
finishes with a `CASE` (NaN, `+∞` or the sum) has the margin check again. The
`CASE`'s conditions must compare a key, a count, an integer sum, a minimum or a
maximum with a constant, combined with `and` and `not`; a condition that reads a
variance, a quantile or another measure the engines compute differently has no
check (#341, #929).

### Correlated `EXISTS` and `NOT EXISTS` lift

A correlated `[NOT] EXISTS` that is a conjunct of `WHERE` lifts as a semi (anti) join of the outer relation
with the subquery's `FROM`, on the conjuncts that read the outer query's columns; the others filter the
subquery's side. Names resolve innermost first. The shapes that stay refused name what to write: a `GROUP BY`,
`HAVING`, `DISTINCT`, `ORDER BY`, `LIMIT` or a computed select list in the subquery, an `EXISTS` under
`OR`, `CASE` or `NOT (… AND …)` or in the select list, an outer reference in a join's `ON` or in a nested
subquery. Correlated `IN` and `NOT IN` follow
([#345](https://github.com/AlexanderNenninger/substrait-lean/issues/345), [#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

### Correlated `IN` and `NOT IN` lift

`x [NOT] IN (SELECT k FROM r WHERE …)` that reads the outer query's columns, as a conjunct of `WHERE`, lifts as a
semi (anti) join. `IN` is a semi join on `x = k AND p`; `NOT IN` an anti join on
`p AND (x = k OR x IS NULL OR k IS NULL)`, so a NULL needle or a NULL in the subquery's column keeps SQL's three-valued
answer (a row stays only if no row of the subquery with `p` TRUE equals `x` or makes the comparison NULL; an empty
result keeps it, also for a NULL `x`). The subquery's shapes are those of correlated `EXISTS`; one that reads the
outer query in its select list, returns two columns or sits under `OR` or in the select list is refused by name
([#345](https://github.com/AlexanderNenninger/substrait-lean/issues/345), [#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).

### Casts of booleans and dates to VARCHAR

`CAST(b AS VARCHAR)` of a boolean gives `true` or `false`, and of a date gives `YYYY-MM-DD`, in Ibis and in DuckDB SQL, with constants folded ([#346](https://github.com/AlexanderNenninger/substrait-lean/issues/346)). Polars refuses the date cast, since it has no cast from a date to a timestamp ([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)). Casts of timestamps and decimals to strings stay refused until their text is decided.

### Casts of decimals to VARCHAR

`CAST(x AS VARCHAR)` of a `DECIMAL(p, s)` now verifies and runs on DuckDB, Polars and Spark: `-` for a negative value, an integer part of at least one digit, then `.` and exactly `s` digits (`0.500`, `-0.05`). A `DECIMAL(p, p)` on DuckDB is widened by one digit first, because DuckDB prints it without the integer part; at `DECIMAL(38, 38)` the report refuses DuckDB and names a cast to `DECIMAL(38, 37)` as the way through. A lifted `CAST(DECIMAL(p, p) AS VARCHAR)` is refused too. Casts of timestamps to VARCHAR stay refused until [#323](https://github.com/AlexanderNenninger/substrait-lean/issues/323); the message names `strftime` with an explicit format ([#346](https://github.com/AlexanderNenninger/substrait-lean/issues/346)).

### The SQL lift reads `time_bucket`

DuckDB SQL with `time_bucket(width, ts[, origin])` lifts for a constant width of days or less (part of [#347](https://github.com/AlexanderNenninger/substrait-lean/issues/347)). The buckets count from DuckDB's default origin (2000-01-03), a constant timestamp origin, or the default plus a constant interval, and agree with DuckDB on negative and NULL timestamps. A width in months, a `DATE` argument and a computed origin are refused. A call spelled `date_bin`, which DuckDB 2.0.0 does not have, is refused.

### The SQL lift reads `time_bucket` by months and of a DATE

DuckDB SQL with `time_bucket(width, ts[, origin])` now lifts for a constant width in months or years, and for a `DATE` argument (part of [#347](https://github.com/AlexanderNenninger/substrait-lean/issues/347)). A month width counts from the origin's month (default 2000-01) and returns the first of the bucket's first month; a `DATE` with a width of whole days or months stays a `DATE`, unless the origin is a timestamp. A year before 1 or after 9999 raises where DuckDB goes below year 1. A width mixing months and days, a sub-day width of a `DATE`, and an interval origin of a month width are refused.

### Timestamp delta verifies

`ts.delta(other, unit)` for microsecond, millisecond, second, minute, hour and day counts the unit boundaries crossed ([D58](docs/decisions.md#d58-a-timestamps-delta-counts-the-unit-boundaries-crossed)), as DuckDB's `date_diff` does. It runs on DuckDB; other engines refuse it with "see #271". Week, month, quarter, year and nanosecond stay refused ([#60](https://github.com/AlexanderNenninger/substrait-lean/issues/60)).

### A timestamp plus a column's interval verifies

`ts + col.as_interval("h")` (a count of days or less, from a column) is accepted for a timestamp, as it already was for a date, and runs on DuckDB. Other engines refuse it with "see #271" until their writers are lowered ([#60](https://github.com/AlexanderNenninger/substrait-lean/issues/60)).

### The reported float bounds are computed exactly

The checker evaluates the bounds behind `Report.epsilon` in exact rational
arithmetic, with square roots rounded outward and each bound written as a
decimal at least the bound
([#660](https://github.com/AlexanderNenninger/substrait-lean/issues/660)).
The `1 + 2⁻⁴⁰` factor that covered an evaluation in doubles, an unproved
step, is gone, so the bounds are slightly tighter in their last digits.
Verdicts do not change.

### Every condition verify cannot read is named at once

`verify` reads every `requires` and `ensures` condition before it proves
anything. If some cannot be read (an unknown column, SQL the lift does not
read, a construct outside the model), it raises one
`sverify.errors.ConditionError` (an `UnsupportedError`) whose `.errors` maps
each such condition's label to its own refusal; the query is not refused
([#699](https://github.com/AlexanderNenninger/substrait-lean/issues/699)).

An Ibis condition that does not type-check, or names a column the table lacks, raised
`TypeError` or `AttributeError` before and now raises `ConditionError`, a
`ValueError`: `except TypeError` around `verify` no longer catches it.

### A refusal names its construct as data

`UnsupportedError` carries `construct` (`"function md5"` for a function,
otherwise SQL keywords in upper case such as `"WITH RECURSIVE"`) and `sql` (the
fragment the SQL lift refused; None for the Ibis producer), keyword-only and
None where a refusal sets none. The text of the error is unchanged. The Ibis
aggregates set `construct` first; the other refusals of the lift and the
producer follow
([#700](https://github.com/AlexanderNenninger/substrait-lean/issues/700)).

### Qualified table names in `tables`

`verify`'s `tables` keys may be qualified (`"shop.main.orders"`, `"main.orders"`). A query's reference matches a key as DuckDB resolves names (catalog, schema, table, with the defaults `memory` and `main`), and the same table name in two schemas stays two inputs. A name outside the inputs is refused with the key to add (#706).

### assert_contract takes the Ibis table a transform returned; SARIF results carry fixes

`sverify.testing.assert_contract` and `assert_engines_agree` take the Ibis table a contracted transform returns on Ibis tables (`assert_contract(paid(orders))`), as well as a node; `data=` gives the rows of the tables it reads, as Arrow tables, dicts or tuples ([#711](https://github.com/AlexanderNenninger/substrait-lean/issues/711)). Checking the test data and the output evaluates a table's Ibis conditions in one query.

`sverify check --format sarif`: a transform's first `needs` result carries a SARIF fix, the edits `check --fix` makes to its `requires=` ([#793](https://github.com/AlexanderNenninger/substrait-lean/issues/793)).

### Spark runs an AVG of decimals

A plan with an `AVG` of a `DECIMAL` (or Ibis's decimal division by an integer) now runs on Spark, where it was refused. Sverify writes the exact quotient at the reference's scale, rounded half away from zero; Spark's own `/` rounds once at a scale of its own first (spark-decimal-arith). A result past 12 decimal places, past 32 integer digits, or of 38 digits with more than 6 decimal places stays refused, with a cast to fewer digits as the way out ([#739](https://github.com/AlexanderNenninger/substrait-lean/issues/739)).

### Spark's refusal of a time of day names the setting

A plan with a time of day (`TIME`) refused on Spark now says why: Spark 4.3 reads `TIME` only with `spark.sql.timeType.enabled` on (spark-time-type). The old message said `TIME` needed Spark 4.1 and named the internal kind `tod` ([#739](https://github.com/AlexanderNenninger/substrait-lean/issues/739)).

### `to_substrait()` exports ordering comparisons of doubles (#741)

`<`, `<=`, `>`, `>=` and `between` on doubles are written with NaN greatest and
the two zeros one (ST-4), as equality, sort keys and grouping keys already were.
`t.filter(t.w > 1.0)` no longer refuses the export.

### The guide is split into one page per task

The guide page is gone. The how-to material is `docs/tasks.md`, now an index, and one page per task (`docs/how-to-contracts.md`, `how-to-guards.md`, `how-to-bounds.md`, `how-to-command-line.md`, `how-to-nodes.md`, `how-to-quarantine.md`, `how-to-table-formats.md`, `how-to-credentials.md`, `how-to-openlineage.md`, `how-to-time-buckets.md`, `how-to-engines-and-sql.md`, `how-to-export.md`, `how-to-production.md`, `how-to-install.md`). `python/README.md` is the short entry: what sverify does, one example, install and links; what the checker proves is in `docs/what-sverify-proves.md` and the status in `docs/stability.md`. `test_readme.py` fails a tutorial or how-to page over 600 lines ([#753](https://github.com/AlexanderNenninger/substrait-lean/issues/753)).

### Opposing pairs in three reference pages

`docs/reference-semantics.md`, `docs/engine-profiles.md` and `docs/optimizations.md` state nine claims without an "X, not Y" pair or an "instead of" ([#754](https://github.com/AlexanderNenninger/substrait-lean/issues/754)). Every fact, identifier, link and number stays.

### sverify check --against-sink: contract drift

`sverify check <file>[:<node>] --against-sink` compares each stored node's contract with the one its sink last committed. A committed promise the node no longer proves (a NOT NULL column, a CHECK, a unique key) is a `contract_weakened` finding at error level, so the check exits 1; a reworded CHECK the node still proves, a smaller key, and a condition inserted before the others are no drift. A changed plan or profile is a `plan_changed` note. The JSON gains `drift`, per node, with what was weakened and added. Without the flag `check` opens no sink ([#769](https://github.com/AlexanderNenninger/substrait-lean/issues/769)).

### A GitHub Action for `sverify check`

`actions/check/` is a composite action that installs `sverify`, runs `sverify check --format sarif` on each target with the default 30 s timeout, merges the logs into one SARIF run and uploads it to code scanning (part of [#770](https://github.com/AlexanderNenninger/substrait-lean/issues/770), item 1). Its job exits with the worst code of the targets', and the `action` job of CI tests it on two example pipelines, one proved and one not, with the PyPI release and with the checkout. `require-proved` needs sverify 0.9.0 and says so. [Checking without running](../docs/how-to-command-line.md#in-github-actions) says how to use it.

### A status page per pipeline in the pipeline template

The pipeline template's catalog now has a phone-friendly status page for each pipeline, `status-<file>.html`. It shows the last refresh (with a link to its run), the rows each node wrote and stores, the contract the check proved, and the next scheduled refresh, read from `refresh.yml`'s schedule. The existing `pages` workflow publishes it with the catalog ([#771](https://github.com/AlexanderNenninger/substrait-lean/issues/771)).

### An AWS session reports its own scope

`Storage` fills `reads` and `writes` from the session when they are not declared: with `boto3` installed, sverify asks STS who the session is, reads the `GetObject` and `PutObject` grants of that role's or user's policies and keeps the prefixes, once per credential. `sverify check` then warns with `[scope]` about a sink outside `staging/` without a `writes=` declaration. A `Deny`, a condition or a pattern that is not a prefix leaves the scope unknown ([#778](https://github.com/AlexanderNenninger/substrait-lean/issues/778)).

### One error for running out of memory

`sverify.errors.MemoryLimitError` (code `memory_limit`, a `MemoryError`) is raised when a step runs out of the memory allowed it: the checker past `SVERIFY_CHECKER_MEMORY_MB` during a proof, or DuckDB past its `memory_limit` (`SVERIFY_MEMORY_LIMIT`, `--memory-limit`) during a run or a refresh, which then commits nothing. `.stage`, `.limit` and `.setting` say which. The command line exits 5 with code `memory` for both; a checker over its cap exited 6 (then the error code) before. Sverify sets no memory default of its own, and the limit does not reach Polars; with `--engine polars` the command says so ([#783](https://github.com/AlexanderNenninger/substrait-lean/issues/783)).

Report text prints a large double constant as Python writes it (`value * 1e+302`), not its 303 digits, and the pipeline template's check loop names the two `overflow` cases `--fix` cannot write a bound for ([#885](https://github.com/AlexanderNenninger/substrait-lean/issues/885)).

### sverify-dbt reads mutually_exclusive_ranges

sverify-dbt reads `dbt_utils.mutually_exclusive_ranges` as `sv.non_overlapping`, on plain columns and with an open end written `coalesce(valid_to, L)` when another test keeps every start before `L`. The shop's point-in-time join `orders_with_city` now proves `unique(order_id)` ([#814](https://github.com/AlexanderNenninger/substrait-lean/issues/814)).

### `sv.non_overlapping`: keys through a point-in-time join

`sv.non_overlapping(lo, hi, by=...)` in `requires` states that a table's validity ranges `[lo, hi)` do not overlap per `by`, as in a type-2 dimension. A left or inner join that equates the `by` columns and tests `lo <= x` and `x < hi` (or `hi IS NULL OR x < hi`) then gives each left row at most one partner, and the left side's keys stay keys of the join: the shop's `orders_with_city` proves `unique(order_id)` from the orders' key. The data check is one window query over the ranges ordered by start. Closed ends (`x <= hi`) have no rule. Incremental views refuse it, as they do `rows_per`.

### Sorts by a double on DuckDB and Spark

The SQL Sverify writes for DuckDB and Spark sorts by a double column itself. It no longer adds a key that ranks NaN apart, since both engines already order NaN above `+inf` as the reference does (#824).

### Engines from plugin packages run by name, with their secrets by reference

`sverify.engines.run(con, plan, "<engine>")` runs a plan on any engine an installed package registers (`sverify.profiles`, `ProfilePlugin.runner`). An engine's runner that needs credentials declares them (`ProfilePlugin.credentials`): each run hands it `sverify.io.Secret` references, resolved by the configured resolver (#775), never values, and `run(credentials={...})` points one at another secret. A refresh on a plugin engine that keeps no pipeline state is refused by the engine's name, with the engines that have one and the one-shot run in the message. `PLUGIN_API` is 5: engine packages need the same release.

### sverify-dbt checked against dbt packages' own projects

`python -m sverify_dbt.replay` builds the integration projects of dbt-utils
1.4.1 and dbt-expectations 0.10.10 with dbt on DuckDB and checks them with
sverify-dbt, test by test, beside dbt's own result. No proved test fails in
dbt's run. The ledgers in `dbt/replay/` name an issue or a design reason for
every test sverify-dbt does not check; CI's `dbt` job replays them and warns
on a change ([#859](https://github.com/AlexanderNenninger/substrait-lean/issues/859)).

### An integer cast to a timestamp in Ibis means seconds

Ibis reads `t.i.cast("timestamp")` as seconds since the epoch, as its DuckDB
backend's `to_timestamp` does; sverify read microseconds, so it proved and
ran a plan whose meaning differed from Ibis's. Sverify now reads seconds,
as `as_timestamp("s")`, and refuses `try_cast` and a time zone there
([#860](https://github.com/AlexanderNenninger/substrait-lean/issues/860)).

### Ibis's own tests replayed through sverify

`sverify_dev.ibis_replay` runs Ibis 12.0.0's backend tests on DuckDB and
verifies and runs every expression they execute through sverify, against
Ibis's own rows: 431 tests agree, none disagree, and each of the 594 refused
names its issue or why it is refused by design
([#860](https://github.com/AlexanderNenninger/substrait-lean/issues/860)).
The replay found two bugs. Ibis's cast of an integer to a timestamp reads
seconds since the epoch, where sverify read microseconds (fixed in its own
change). A run refused a table with a float32 column the query never reads
when it checked a precondition; the check now reads only the columns the
preconditions read, as SQLGlot finds them.

### Exported plans pass Substrait's validator

`report.to_substrait()` writes plans `substrait-validator` accepts: a
projection that only reorders columns becomes its input's output mapping, a
typed NULL is nullable, a constant table's values have its columns' types, an
`if_then`'s NULL or decimal constant takes its other branches' type, and the
plan declares the contract message it carries (`expected_type_urls`). A
precondition on a text column (`reverse` needs ASCII) no longer fails the
export, and `from_substrait` checks it again. Exports ask the checker's
transfer check once per process, about six times faster. CI validates every
coverage case and catalogue query with the validator and records the result
in a ledger ([#862](https://github.com/AlexanderNenninger/substrait-lean/issues/862)).

### ODCS's published examples read

`sverify.odcs.read` is checked against the 42 example contracts the Open Data
Contract Standard publishes for v3.2.0: 151 conditions read, every unread rule
with its reason and issue, and 95 of the schema objects export and read back
to the same conditions ([#864](https://github.com/AlexanderNenninger/substrait-lean/issues/864)).
`read` now takes a quality rule's SQL that names its object (`SELECT COUNT(*)
FROM orders WHERE …`, in any case), and leaves unread a timestamp bound with a
time zone on a column without one, which DuckDB's cast would have dropped; a
bound on a column with a time zone is cast to `TIMESTAMPTZ`.
A physical type that DuckDB reads as an array (`varchar[3]`) becomes an array
only where the logical type says `array` or says nothing; under `string` it is
a string, as ODCS's AdventureWorks example means it.

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

### sverify-dbt checks a model that reads an ephemeral model

dbt inlines an ephemeral model into each reader as a CTE, so the reader's compiled SQL names the ephemeral's inputs. `sverify-dbt check` now reads those inputs through the ephemeral model, transitively, instead of refusing the reader with "a hard-coded table name"; the ephemeral model itself prints a note saying which models it is inlined into (#891, 1.4).

### `sverify-dbt check` exits as `sverify check` does, and a refused model no longer fails the default gate

A model sverify cannot read (`WITH RECURSIVE`) with an enforced contract failed `--fail-on contract` on every run, and its text showed no reason. It now prints its constraints as not checked, and the gate fails only on a constraint that is not proved. The `--fail-on` levels nest: `contract` (the default), `unproved` (also any test not proved) and `refused` (all of that, and exit 3 where a model is refused). `--fail-on unproved` no longer fails on a refused model, which it did; use `refused` for that. An unreadable project is exit 2, an unsupported check 3, a broken install or an I/O error exit 8 with its message, where it was a traceback and exit 1, the code for "a contract does not hold" (#891, 1.2 and 1.3).

### `sverify check <dbt dir> --format json` works

`sverify-dbt check` takes `--format text|json` (`--json` stays as the alias), the flag `sverify check` forwards to it. For a dbt project `sverify check` prints text or JSON; `--format github`, `sarif` and `junit` stop with a usage error instead of reaching sverify-dbt's parser (#891).

### `sverify-dbt check` prints for CI and takes sverify's budgets

`sverify-dbt check --format github|sarif|junit` prints one annotation per finding on the model's file, a SARIF 2.1.0 log, or a JUnit suite per model. `--timeout` and `--memory-limit` bound the check as they do in `sverify check`, which now passes both through for a dbt project; a check past either exits 5. The time limit is off unless `--timeout` or `$SVERIFY_TIMEOUT` sets it: a project check is many models, and `sverify check`'s 30 s is per file (#891).

### sverify-dbt stops on a mismatched sverify, and warns on an older manifest

`import sverify_dbt` raises an `ImportError` naming the two versions when the installed `sverify` is not at sverify-dbt's version, instead of failing deep inside a check. `check` warns when `manifest.json` is not schema v12 (dbt-core 1.10 to 1.12), where it attaches tests by guesswork. The README's sample output is what `check` prints on `examples/shop` (every `accepted_values` test there is proved now), a test keeps it so, and `PROOF-STATUS.md` has the current counts, 23 of 26 (#891, 1.7 and 1.8).

### `sverify-dbt check --selectors` needs the whole project

`--selectors` with `--select` stops with a usage error, and `CheckResult.write_selectors` raises `ValueError` after a partial check: the selector would have replaced the proved tests of every model outside the selection, and `dbt build --exclude selector:sverify_proved` would have run them all again without a word (#891, 1.6).

### DuckDB's quantile_cont stays inside the model near whole positions

DuckDB computes the position `(n − 1)·q` of `quantile_cont` in a double, which can miss the exact position's floor or ceiling when the exact position is within `(n − 1)·2⁻⁵¹` of a whole one. In that band the written plan now takes `quantile_disc` of `q` moved by 10⁻¹⁵ toward 1/2, whose index is the nearest whole position, and raises `domain` where the neighbours are `-inf` and `+inf`. This replaces the refusal of `quantile(1/3)` (Ibis writes 16 decimals) from two values: the writer now refuses a fraction of more than 21 decimals, and a group of 10¹⁴ values or more ([#900](https://github.com/AlexanderNenninger/substrait-lean/issues/900)).

### DuckDB's quantile_cont stays inside the model at a whole position

DuckDB computes the position `(n − 1)·q` of `quantile_cont` in doubles, so where the exact position is whole and its double is not (n = 26, q = 0.28), it interpolates toward the next value: of the values 1.0 then 1e300 it gave 8.9e284 where the model says 1.0. The written plan now takes `quantile_disc` at a whole exact position, and bounds the result by the second smallest value where the lower neighbour is the first, with the guards in exact integer arithmetic ([#900](https://github.com/AlexanderNenninger/substrait-lean/issues/900)).

### DuckDB's quantile_cont is stated as what it computes, and its route is a shim

`quantile_interp`'s `LINEAR` (DuckDB's own `quantile_cont`) now takes the neighbours of its double position `(n − 1)·q` and an ulp past them where the lower neighbour is first, where it read "between the neighbours". The written plan's guards (`Dialect.quantile`) are the shim `quantile_guard`, with the precondition `(COUNT(x) − 1)·10^scale < 2^52` checked on the data, so a DuckDB `quantile_cont` route reports class `shim` where it reported `exact` (the evidence stays tested, tracked in [#900](https://github.com/AlexanderNenninger/substrait-lean/issues/900)).

### Fixed

- A node over a source that cannot restore (`from_frame`) no longer rewrites its sink when the sink's record is at a higher version of the same contents. The record's digest says the rows are the state, and the writer skips, as the model of the refresh protocol decides ([#933](https://github.com/AlexanderNenninger/substrait-lean/issues/933)).

### Decimal literals of up to 38 digits are written exactly

A decimal literal of more than 28 digits was rounded to 28 by Python's default `Decimal` context and then refused as "does not fit" its type. The scaling now runs in one context wide enough for 38 digits (`sverify._decimals.scaled`), so such a literal, a bound of `10**34 - 1` for example, verifies and compares exactly. Other places that shared the rounding (the Ibis producer's literal width, the shown bounds of a decimal) use it too.

### `lean_values` raises on filters and aggregates too

`sverify.testing.lean_values` raises `LeanRaised` where the reference raises in a filter condition, a projection or an aggregate's groups and arguments, at any depth of the plan (`substrait-check --raises`). Joins and windows are not looked into.

### `lean_values` raises where the reference raises

The internal test oracle `sverify.testing.lean_values` returns `Rel.eval`'s rows, which have a value where the reference raises (a cast that does not fit gives `NULL` or an out-of-range integer). For a projection over a `VALUES` it now raises `LeanRaised` with the error (`substrait-check --outcomes`). Other plan shapes are not checked.

### Snowflake: a `-0.0` literal keeps its sign

Snowflake's SQL writes double literals as the other writers do (the base writer's `float_lit`): a `-0.0` literal is `CAST('-0.0' AS FLOAT)` and keeps its sign (D31), where it was written `0.0`; infinities are spelt `'Infinity'`. A sign-sensitive use of the literal (`atan2(-0.0, -1.0)`) now gives the reference's value on Snowflake. The DuckDB and Polars facts on `round`, `floor` and `ceil` now state the reference's `round_zero_sign` (left open; `eval` gives `+0.0`) and `zero_sign` (`ONE_ZERO`).

### Snowflake: a regex search of the empty string

Snowflake's SQL writes a regex search as `REGEXP_COUNT(s, p) > 0` instead of `REGEXP_INSTR(s, p) > 0`, which is false on an empty string even when the pattern matches it (`^$`, `x*`), so `re_search` of `''` now gives the reference's TRUE.

### Spark no longer keeps a view for every change it merges into a state

Merging an Arrow change into a view's state on Spark registered the change as a temporary view that nothing dropped, so the Spark JVM kept the rows of every refresh until the session ended. A pipeline with large changes ran the driver out of its default 1 GB heap, and the JVM then hung instead of failing. The change now goes to Spark as a frame that no view names.

### Other changes

- A `rows="sequence"` postcondition on an unsorted result now names its exits: sort the result with `order_by` on a key, or state `rows="multiset"`.

- The float bounds page explains what a postcondition on a double asks of a route: a bounded column is refused with the exit `sv.approx`, an unbounded one lets a sign-only claim run and refuses a stated tolerance, and a threshold on a double refuses the plan. Notebook 05 shows the unbounded case.

- A refresh after a small change to an Arrow-fed source no longer costs a pass over its input (#1329): on DuckDB the sealed input takes the change in place, as a view's state does, and the input is moved into the store at the first load. The refused delete names its row again ("cannot delete rows from `t`: no such row ...").

- Arrow-fed sources (`StaticSource`, `sverify.io.Source`) now keep their rows in the store of the pipeline's engine, not as an Arrow table beside it (#1329): a refresh adds the change in the store, and a delete that finds no row raises "cannot delete rows from `t`: no such row" without naming the row.

- Every guard a SQL writer emits (`Dialect.raise_`) now names the `Issue` it enforces, and a test ties each written guard to an issue the checker reports for the plan. A dialect that overrides `raise_` takes the extra `issue` argument. The substring-offset guards enforce `domain`, as `Safety` reports it; Snowflake's `SUM` check enforces `sumWraps`.

- DuckDB's table states what it does at `list_null_order`: a NULL element sorts greatest, its `<` of lists is shimmed to the reference's NULL, and its MIN and MAX agree with the reference, so an integer `MAX` now transfers at DuckDB. Spark and Polars order a NULL element least; their rows wait for the option's scope to narrow to list arguments (ruling 171), because a refused row would refuse every MIN and MAX today.

- The sverify-dbt measurement page declares the suggested `not_null` on `stg_orders.customer_id` (jaffle_shop: 14 of the project's 20 tests proved) and names the four Cal-ITP models with no compiled SQL.

- Added `dbt/scripts/measure.py` and `docs/dbt-measurements.md`: sverify-dbt measured on jaffle_shop and Cal-ITP's warehouse (models read, tests proved, test queries skipped), with the column types supplied for Cal-ITP.

- The guard of `UPPER`, `LOWER`, `ILIKE`, `reverse`, `ascii`, `levenshtein` and class regexes tests one predicate (`ascii_text`), shared with the ASCII precondition the report will infer; a regular expression with `\w`, `\d`, `\s` or `\b` also raises on a vertical tab, where Rust's classes and RE2's differ (`Text.classesDiffer`).

- `UPPER`, `LOWER`, `ILIKE`, `reverse`, `ascii`, `levenshtein` and class regular expressions (`\w`, `\d`, `\s`, `\b`) on text that is not known to be ASCII are reported as the issue `non-ASCII text` (`Issue.nonAscii`, D43) and no longer proved: the report suggests the precondition that the column is ASCII (without a vertical tab for a class), and `Report.check_inputs` checks it on the data. The writers' guard raises on the same predicate as before.

  A plan with one of these on a column the contract does not declare ASCII changes its verdict from proved to unproved under every `semantics`; declaring the column ASCII in `requires` (the report prints the condition) restores it. Under `semantics="substrait"` the new option `non_ascii_text` allows `COMPUTE`, so the functions of the new group `str.ascii` (`reverse`, `ascii`, `levenshtein`, `ilike` and the regular expressions) need the condition there too. Substrait's own `reverse` test cases on non-ASCII text are now disagreements of the ledger (`upstream/substrait-cases.json`).

  Under `semantics="substrait"` the nine functions that can report the issue (`upper`, `lower`, `reverse`, `ascii`, `levenshtein`, `ilike` and the three regular-expression functions) are unproved on `non_ascii_text` with or without the ASCII condition declared: the transfer is static, as for `substring_range`.

- A column of a narrow integer type (`TINYINT`, `SMALLINT`, `INTEGER`) is known to lie in its type's range, as a `BIGINT` column already was (D46). `CAST(i AS BIGINT) * 4` over an `INTEGER`, or an `INTEGER` substring offset, no longer needs an inferred precondition on the column's range; the run's schema check (#1540) holds the data to the declared type.

- `CAST(i AS BIGINT) * 4` over an `INTEGER` column is now 64-bit arithmetic in the model and is proved with no bound. The parser read a cast to an integer type as the width of its operand and modelled the product as `WRAP32`.

- In Ibis, the calendar functions of a UTC timestamp (`date()`, `time()`, the casts to a date and a time, `year()` and the other extracts, `epoch_seconds()`, `truncate`, `bucket` and `strftime`) now run on its UTC wall clock, whatever the session's time zone (D69, #1725). Arithmetic with intervals, the difference of two instants and the cast to a string stay refused.

- The Spark engine's and the file scans' refusals end with what to do instead: run it with `engine='duckdb'`, split the query, declare the column's file type, or use a local file. The test that every refusal names a fix covers the engines.

- Refusals of the Ibis and SQL frontends end with what to write instead: a literal in place of a column where a constant is needed, a column to order by, or a rewrite with a supported operation. A test checks that every frontend refusal does.

- Refusals of the SQL writer end with what to do instead: a literal in place of a column where a constant is needed, or a rewrite of the step. A test checks that every writer refusal does.

- A Polars left join raises where its condition raises on a pair that passes the other comparisons, as the inner, semi and anti joins and DuckDB do (#1857). The left join read its matches twice, which made Polars cache them and fuse the filter into a nested-loop join below the raise check, so the check never saw a pair the comparison rejects. It now reads them once.

- A pipeline node refreshed on Spark keeps its view's state in Spark's store from its first state on (#1881). Before, the view was built on the DuckDB connection the stage reads its sources through, so its state was a DuckDB table and every merge moved the view's rows through DuckDB in the driver.

- Ibis: a substring whose length comes from a column is refused with a message that says to use a constant length or `ifelse`. The replay ledgers are rewritten: the multi-quantile, mode, `count_distinct_star`, arbitrary, ordered first/last and expression-window rows now agree or are unproved.

- A cast of an integer count of seconds, milliseconds or microseconds to a
  timestamp now raises (`overflow`) where it lands outside 0001 to 9999, the
  reference's timestamps (D32). Sverify reports it as an issue unless the
  count's bounds rule it out, and the written SQL and the Polars plan raise at
  run time. Before, such a cast was proved with no precondition (#1947).

- `log(x, base)` with a NULL argument is NULL at DuckDB, Spark and Polars, also where the other argument would raise (`log(NULL, 0)`, `log(NULL, 1)`), as the reference reads a call with both arguments present only (#1990). DuckDB's written SQL raised there, since its raise helper does not return NULL for a NULL guard column; the shared writer and the Polars lowering now guard the domain check against a NULL argument. `log(1.0, 0)` still raises.

- A plan whose timestamp, instant or time-of-day column has a precision other than microseconds (`precision_timestamp(9)`, `precision_time(3)`) is refused when it is read. The checker used to read a nanosecond count as microseconds, so a comparison of `precision_timestamp(9)` with `precision_timestamp(6)` compared raw counts of different units (#2004). Literals finer than microseconds are refused too. D61 is recorded in `docs/decisions.md`.

- - Fixed: a postcondition that reads a list column was proved under a lens that ignores the order of a list's elements (`elements="multiset"`, the plan bound) though a lens-equal result can falsify it (`list_position(pair, a) = 1`). The report now lists `elements` among what the condition depends on and the observation ignores (#2005).

- A typed decimal NULL literal in a Substrait plan reads with its declared decimal kind, so calls of only such NULLs (`negate`, `abs`, `add`, `coalesce`, `nullif` and the others) are read instead of refused as "a DECIMAL result of non-decimal arguments" (#2026).

- The facts that DuckDB 2.0.1 changes were probed again (#2045), and 2.0.1 is still not a probed version: runs on it keep their `EngineVersionWarning` until the rest of its test tree is replayed. A constant `WHEN` that raises no longer raises while planning (DD-7 is fixed upstream), `MIN % -1` returns 0 instead of raising, `fsum` and `favg` of an infinity give the infinity, and `list_contains([], NULL)` gives FALSE where 2.0.0 and the model give NULL. The DuckDB writer now guards the needle of `list_contains`, so a plan gives NULL at both versions, and the report lists the construct when SQL is read natively. `string_split('', '')` is `[]` at 2.0.1 and `['']` at 2.0.0, and Lean no longer evaluates that cell. The 2.0.0 facts stay for users still on it.

- Fixed: a CTE named like a table it reads (`WITH t AS (SELECT a FROM t) ...`) no longer crashes the SQL lift with a `RecursionError`. A CTE's body sees the tables and the CTEs defined before it, as in DuckDB.

- A run-time check that fires during `sverify refresh` (a product that overflows to infinity, a guard of the plan) now holds the node: exit 7 and the held alert, which names the check and says what to state in `requires=`. It was an error, the code for a crash. A direct `Report.run` still raises the engine's error, and `sverify check` says as before that the plan raises at run time. The run stopped part-way, so the node's in-memory state is dropped: at its next refresh a node with a sink resumes from the sink, and a node without one starts from scratch.

- A `BETWEEN` of a `BETWEEN` in a SQL query lifts to a plan whose size is linear in the nesting depth. Each level doubled the plan, so thirty levels never finished.

- A Delta sink no longer refuses its own constraint on the refresh after an insert-only change when the node's ensures is `isnull() | (>= 0)` on a column that is never NULL: Delta stores that constraint without its `IS NULL` part, and the sink now compares the two as the same condition.

- A fourth agent skill, `sverify-patterns`, writes common data engineering patterns with the contract each proves: deduplicating, sessionizing, reconciling and double entries, funnels, floating point aggregates, slowly changing dimensions, running balances and FIFO matching, counters and time-weighted averages, and gap filling. Each reference gives the rule in Ibis and SQL, and its code runs in the tests.

- The dbt replay covers the projects inside `dbt-tests-adapter` 1.20.0's pytest classes (175 distinct projects, 128 tests: 8 proved, none unsound), beside dbt-utils and dbt-expectations ([#859](https://github.com/AlexanderNenninger/substrait-lean/issues/859)). sverify-dbt refuses a model whose compiled SQL does not tokenize, where it crashed.

- The dbt replay ledgers are refreshed: dbt-utils now proves 3 tests (was 1) and dbt-expectations reads its row-level tests ([#859](https://github.com/AlexanderNenninger/substrait-lean/issues/859)). `replay/constructs.json` names the issue or design reason of each refusal.

- `python -m sverify_dbt.replay --check` also reports a ledger entry that waits on a closed issue ([#859](https://github.com/AlexanderNenninger/substrait-lean/issues/859)).

- sverify-dbt refuses a model that reads a table function such as `read_csv('…')`, naming it, before DuckDB plans the SQL: DuckDB opened the file or URL when it bound the function ([#891](https://github.com/AlexanderNenninger/substrait-lean/issues/891)). `range(…)` is still read.

- The repository variable `AWS_RUNNERS=off` skips CI's `aws-probe`, so every job runs on GitHub's runners.

- `UPPER` and `LOWER` map each Unicode scalar value as DuckDB, Polars and Spark all map it, and raise only on the scalars they map differently ([D51](docs/decisions.md)): 157 for `UPPER`, 57 for `LOWER` (the 56 that differ and every `Σ`, whose mapping depends on its context). The raise is the new issue `Issue.caseDiffers` (`text the engines' case mapping treats differently`) under the new option `case_mapping` (`ERROR`, `COMPUTE`; Substrait's is `COMPUTE`), no longer `Issue.nonAscii` under `non_ascii_text`. `ILIKE`, `reverse`, `ascii`, `levenshtein` and the regular expressions keep D43.

  A plan with `UPPER` or `LOWER` on a column that is not declared ASCII is no longer unproved: the report suggests the precondition that the column is in the function's agreed alphabet, with none of the scalars it raises on (`upper_agreed`, `lower_agreed`; ASCII implies both); the checker's request names the declared text facts under the key `text`, a list per column, and `Report.check_inputs` checks it on the data on DuckDB, Polars and Spark, the supplementary-plane scalars included. `é`, `Ω` and the rest of the agreed alphabet pass. The reference's `Text.upper` and `Text.lower` are definitions over a generated table (`python -m sverify_dev.case_mapping`, `core/Sverify/Core/CaseTable.lean`), not black boxes.

  Spark's writer calls `collate(upper(collate(x, 'UNICODE')), 'UTF8_BINARY')`, which does not follow the JVM's default locale. Snowflake's writer refuses `UPPER` and `LOWER` of anything but a literal until its case mapping is recorded. The guards of DuckDB and Spark raise on the same scalars the issue reports.

- The case-mapping tables of DuckDB, Polars and Spark are recorded (`engines/<engine>/probes/case-tables.json`, `characterization/case-differences.json`, `sverify_dev.case_tables`): 213 Unicode scalar values differ between the engines (157 for `upper`, 56 for `lower`), all of them DuckDB's simple mapping against the full one Polars and Spark share, plus the final sigma as a context rule.

  Spark's case mapping is recorded by its source: ICU's `UCharacter` under the default `spark.sql.icu.caseMappings.enabled`, the JVM's `String` under `false`, both in the JVM's default locale. The tables agree across pyspark 4.0 to 4.3, the two paths and the default locale; under a Turkish, Azeri or Lithuanian JVM locale `lower` (and, in a string with a non-ASCII scalar, `i` and `I`) map otherwise (`engines/spark/probes/case-tables-settings.json`). Polars's source is cited, and `tests/test_case_tables.py` re-probes DuckDB and Polars at the installed version.

  Spark's writer form for `UPPER` and `LOWER` on text not proved ASCII is recorded as a fact (`spark-case-collated`): `collate(upper(collate(x, 'UNICODE')), 'UTF8_BINARY')` maps as the table under every JVM locale tried, on drivers and executors, on pyspark 4.0 to 4.3, and returns a byte-compared string. The plain functions follow the JVM's default locale, against their javadoc (upstream ledger entry SP-9).

- The dbt replay of the adapter suite no longer builds the projects that define no test, and the `dbt` CI job's timeout is 30 minutes.

- Delta sinks and sources work with newer `deltalake` releases, whose `DeltaTable.history` returns an iterator rather than a list.

- On the ARM Hetzner runners, pull request runs only restore caches; `arm-cache.yml` saves the ARM caches on main.

- CI can send its four longest jobs to a fixed Hetzner runner host (label `hetzner`) when the repository variable `HETZNER_RUNNERS` is `on`; off by default.

- The Hetzner runner hosts are x86 (two servers in Helsinki): `hetzner` jobs ask for X64, and `arm-cache.yml` is gone.

- Polars's reciprocal bound for a double division (`x / c`) is now stated only where the divisor is not subnormal, and for every divisor without a column reference, a constant expression included, not for literals alone. Below the smallest normal, `1 / c` overflows on Polars and the plan has no bound; a constant expression such as `7.0 * 7.0` gets the reciprocal's bound where it had the exact quotient's. `rule_div_le_recip` proves the reciprocal's bound is at least the exact one's, so a short frame, which Polars divides exactly, is covered too. Ruling 157.

## 0.8.0 (2026-11-09)

Engines become packages of their own (`sverify-duckdb`, `sverify-polars`, `sverify-spark`), DataFusion is gone, and the reference's floating-point and window semantics are proved further. Some public names moved; the entries below say where.

### DataFusion removed

Sverify no longer supports DataFusion: the `datafusion` extra, its runner and its profile are gone, and `engine='datafusion'` is refused. The entries below that mention DataFusion describe changes made before its removal.

### A sink no longer writes an older state over a newer record

When another process committed a later version of a node between this
refresh's read of its sources and its read of the sink, the refresh took the
higher source version on record for a table dropped and created again, and
wrote its older rows over the newer ones; the next refresh of the other
process put them back (#1025). A lower version of the same table (the same
table id) now means this refresh is behind: it skips, and the sink keeps the
later state. A source whose table id changed is still rewritten in full
(#516). Found by the test that pins `Sink._commit` to the Lean model's
`Refresh.next` (#933).

### Window sums of doubles have the plan's bound

- A window `SUM` or `AVG` of doubles has a bound again: `Report.epsilon`
  gives its column the bound of the input's row cap, as for a grouped one,
  proved under the same conditions
  ([#1032](https://github.com/AlexanderNenninger/substrait-lean/issues/1032)).
  It rests on each engine's window algorithm, a new option
  (`window_sum_algo`) with a fact per engine: DuckDB, Polars and Spark sum
  each frame's own values (a tree, each frame anew, or a running sum). A
  window `VARIANCE` or `STDDEV` still has no bound (#918).
- The options a plan depends on include its windows' sort keys and partition
  keys. A window over a key now takes its evidence from the engine's NULL
  placement row.

### Postconditions on doubles that hold on every engine run

- A postcondition that reads a double `SUM`, `AVG` or statistic, and holds of
  every value within the column's bound and of its sign, now runs on every
  engine, without `sv.approx`. Before, the whole plan was refused with
  "write it as sv.approx(...)", even for `_.total >= 0`
  ([#1045](https://github.com/AlexanderNenninger/substrait-lean/issues/1045)).
  A postcondition that only the reference's exact value meets is still
  refused, naming `sv.approx` as the way out.

### Engine and writer refusals name their exit

- Every refusal of the Polars translator, the DataFusion runner and the
  Spark and Snowflake SQL writers now ends with what to do next:
  `run it with engine='duckdb'` and the issue that tracks the engine, or a
  rewrite where one keeps the result (a cast to fewer digits for Spark's
  decimals). Before, "Spark window functions need an ORDER BY", "Snowflake's
  LN is not documented to be C's libm" or "DECIMAL(40, 2) is not a decimal
  type Polars has" named none
  ([#1047](https://github.com/AlexanderNenninger/substrait-lean/issues/1047)).
- A writer hook a dialect lacks reads "the spark writer does not write
  integer division yet: run it with engine='duckdb' (see #271, …)", in place
  of "spark: integer division is not implemented".

### SQL and Ibis refusals name their exit; Lean's refusals are `UnsupportedError`

- A plan the checker refuses now raises `UnsupportedError` (still a
  `ValueError`), "substrait-check --contract refuses the plan: …", ending with
  the open coverage issues. Before, the Ibis path raised a plain
  `ValueError`, which `except sverify.errors.SverifyError` missed, and
  `sv.sql`, `Report.to_substrait` and DataFusion worded the same refusal three
  other ways ([#1050](https://github.com/AlexanderNenninger/substrait-lean/issues/1050)).
- The SQL lift names a rewrite or an issue for DISTINCT ON, QUALIFY, named
  windows, LATERAL, PIVOT, SAMPLE, JOIN USING, correlated subqueries,
  WITH RECURSIVE, an aggregate of a DATE at midnight and the SQLGlot
  disagreements SG-4, SG-8 and SG-9; the Ibis producer names #60 or #327 for
  an operation it does not map yet
  ([#1049](https://github.com/AlexanderNenninger/substrait-lean/issues/1049)).
- Unsigned integers and zoned or non-microsecond timestamps name a cast and
  their issues (#350, #323).

### The unsigned and zoned-timestamp refusals say where the cast goes

- "unsigned integers (uint32) are not supported yet (#350)" and the
  timestamp refusals now say to cast the column before sverify reads the
  table: an Ibis cast after the read does not help, since the read itself
  carries the type
  ([#1050](https://github.com/AlexanderNenninger/substrait-lean/issues/1050)).

### Refresh, export, sharding and sverify-dbt refusals name their exit

- `NotIncrementalError` from a standalone view names the way out: a view in
  a `Pipeline` (a node built with `.pipe`) is recomputed and diffed instead.
  `AuditError` says what to check and where to report a mismatch; a
  precondition on a view says to state it in the `ensures` of the transform
  that builds it; foreign keys in views name #869
  ([#1051](https://github.com/AlexanderNenninger/substrait-lean/issues/1051)).
- `ExportError` for a relation, expression or function `to_substrait` cannot
  write names `report.to_sql(dialect)`
  ([#1053](https://github.com/AlexanderNenninger/substrait-lean/issues/1053)).
- `NotShardable` for a `SUM` or `AVG` of doubles names
  `run_sharded(reproducible=sv.equivalent(floats="plan"))` in place of the
  deprecated `float_order="any"`
  ([#1054](https://github.com/AlexanderNenninger/substrait-lean/issues/1054)).
- sverify-dbt says that dbt still runs a test it does not map, a foreign key
  of a result or a Python model's tests, how to map it
  (`dbt_utils.expression_is_true`, `{{ ref() }}`), and keeps sverify's own
  exit in a refusal; before, it kept only the message's first line
  ([#1055](https://github.com/AlexanderNenninger/substrait-lean/issues/1055)).
- `sv.asof_join`'s docstring no longer claims operators Lean verifies: the
  join has no theorem of its own and is proved as any plan, by
  `contract_sound_all` and `Rel.keys_sound_all`, which `docs/proofs.md` now
  lists for it ([#1052](https://github.com/AlexanderNenninger/substrait-lean/issues/1052)).

### A sixth tour notebook: running it in production

- [`notebooks/06_running_in_production.py`](notebooks/06_running_in_production.py)
  covers the work around a proved pipeline: `sverify check --diff` and
  `--fix` on a pipeline's file, a test with `sverify.testing.assert_contract`,
  a credential by name (`Secret`), OpenLineage events whose contract the
  next team proves again, and an hourly rollup whose state
  `sv.arrives_within` bounds, with a late batch refused before it lands
  ([#1056](https://github.com/AlexanderNenninger/substrait-lean/issues/1056)).

### The checker decides what a postcondition ignores

- What an observation (`sv.equivalent`) ignores of a postcondition, and which
  open choices of the plan it reads, now come from the checker
  ([#1071](https://github.com/AlexanderNenninger/substrait-lean/issues/1071)).
  That a postcondition does not depend on the sign of a zero is a theorem
  (`Expr.robust_of_depends_canon`) where it was an assumption.
- A postcondition proved on every order of the reference, but not on every
  result it allows, reads an open measure (`VAR_*`, `STDDEV_*`, `COVAR_*`,
  `CORR`, `QUANTILE_CONT`, a double `SUM` or `AVG` added in another order).
  Under an observation other than the plan's bound, its route's evidence is
  now `tested`, not `proved`. Nothing that ran is refused.

### The checker stays within its memory

- `repeat(s, n)`, and Ibis's `rpad` and `lpad` built on it, are evaluated
  into one string. A count such as `10⁹` built a list of `n` pieces first and
  took the checker past 23 GB, which hung a 16 GB laptop; the same request now
  peaks at 3 to 6 GB, a few copies of its 1 to 2 GB result
  ([#1074](https://github.com/AlexanderNenninger/substrait-lean/issues/1074)).
- A checker request that takes `substrait-check` past 4 GB stops the checker
  and raises `CheckerMemoryError` (a `MemoryError`), and the next request
  starts a new checker. `SVERIFY_CHECKER_MEMORY_MB` sets the cap; 0 turns it
  off. The cap applies on Linux and macOS.

### `verify` checks contracts at their earlier speed again

Since the checker's contract check was split into parsing and checking
(#1088), it built every table's knowledge, its schema parse included, again
at each read of each analysis pass, and a contract check took about twice as
long: TPC-DS q27 743 ms where it took 145 ms. It builds that knowledge once per
request again, and gives the same answers.

### One report per checker answer

- `sv.verify` and `sv.from_substrait` build their reports in one place from
  the checker's answer, so a re-checked import now carries everything a
  verified plan does
  ([#1088](https://github.com/AlexanderNenninger/substrait-lean/issues/1088)):
  - its assumed issues (a `SUM` that may leave its type, an overflow to `±∞`)
    are listed in `report.assumed` and checked on the data while the job runs,
    where the import used to drop them;
  - the checks the checker discharged (`unchecked`), the optimized plan, the
    per-relation row bounds, `rows_exact` and the margin checks of threshold
    filters (#929).

### One delta query per batch

- An incrementally maintained view runs its delta plan as one query per
  batch on every engine. The checker used to split it into union-free terms,
  one query each, for DataFusion's Substrait consumer: a 2-table join ran 3
  queries a batch and a 3-table join 7. Batches of the 3-table join now take
  about half the time on DuckDB and Polars.
  `sverify.engines.delta_plans` returns a one-item list.

### Leaner plans and copy-free tables

- Written plans no longer wrap each double operation in `nanvl(x + 0.0, NaN)`
  for DataFusion. Plans of double arithmetic are about a fifth smaller, and
  Polars runs them up to 5 times faster.
  `Report.to_substrait` still gives other Substrait consumers canonical
  doubles (ST-4).
- `Connection.put` stores a table as given, without copying it.

### The checker classifies issues and evidence

- `substrait-check --contract` says per issue whether it is assumed and
  checked on the data while the job runs (`"assumed"`: a `SUM` that leaves
  its type, an overflow to `±∞`), and its exit code no longer counts those as
  unproved: a plan whose only issue is an assumed `SUM` overflow exits 0, as
  sverify's report already said
  ([#1088](https://github.com/AlexanderNenninger/substrait-lean/issues/1088)).
- An overflow to `±∞` is reported only under the reference: under another
  profile the request names (`semantics="duckdb"` included, which sverify now
  sends), the engine gives `±∞`.
- The report's `engines` block gives every engine a route may reach a
  verdict, DataFusion included (`"profile": false`), and says per engine why a
  translated run rests on tests (`"tested_because"`) and what evidence it
  carries (`"translated_evidence"`)
  ([#1166](https://github.com/AlexanderNenninger/substrait-lean/issues/1166)).

### Verified plans run on Polars without the checks the proof discharged

- `Report.run` on Polars leaves out the per-row run-time checks of a
  guard-free plan once it has checked the preconditions on the batch
  (`guard_free`, `Rel.polars_sound`). The checks of assumed `SUM`s and of
  `±∞` stay. On the catalogue's 52 proved plans, Polars's plans hold 107 guard
  columns where they held 206
  ([#1166](https://github.com/AlexanderNenninger/substrait-lean/issues/1166)).
  With `check_requires=False`, and on engines whose writer no theorem covers
  without its guards (DuckDB, Spark, Snowflake), every check stays.

### Every tested engine row names the issue tracking its proof

An engine profile's observation rows that rest on tests or probes, not on a
Lean theorem, now name the issue that tracks their proof, and the checker
refuses a profile with a row that names none (`EngineProfile.tracked`,
#1131, #1166). `--options` and `--realizability` print each row's `issue`
and the engine `version` its facts were checked at, beside its `facts` and
`theorem`. DuckDB's `MIN % -1` row, which the generated lowering entry
covers, is marked proved (`Lowering.duckdb_exact`).

### Routes name their evidence

- A route keeps the provenance the checker gives for its class: `route.theorems`
  for a proof, `route.facts`, `route.version` (the engine version the facts
  were probed at) and `route.issues` (the issues that track them) for a test. Its line names them:
  `shim (integer division rewritten to truncate); evidence proved by Rel.polars_sound, Polars.int_div_trunc`.
  The report's JSON carries the four fields
  ([#1166](https://github.com/AlexanderNenninger/substrait-lean/issues/1166)).
- `print(report)` shows an `evidence:` line per engine before any run, so a
  plan that rests on tested facts on an engine says so before it runs there.
- Evidence is `proved` only where every choice the class rests on is proved in
  Lean; a probe, a row without evidence or an option without a row counts as
  `tested` (the catalogue's `control-max-exact` on Polars is now tested). Before, a plan
  whose rows were all probes read as proved.
- The engine versions come from the checker's profiles alone; the copy in
  `sverify.routes.PROFILES` is gone.

### Routes take the checker's verdict

- The class, evidence, shims and refusals of a route come from the checker's
  verdict per engine (`substrait-check --contract`'s `"engines"`), and the
  transfer route takes the checker's transfer check (`Rel.transfer_of_transferB`)
  over every option the plan reads
  ([#1166](https://github.com/AlexanderNenninger/substrait-lean/issues/1166)).
  A sort whose NULL placement the plan states now transfers to an engine that
  gives it as stated (17 catalogue plans verified under Polars's or Spark's
  semantics now reach DuckDB); an integer `SUM` verified under Spark's
  semantics no longer transfers to DuckDB, whose `avg_int_result` differs in
  the group the check reads.
- A proof of the engine's model names the facts that say the engine is that
  model: `evidence proved by Rel.polars_sound on polars's model (facts …)`.
- A report read back with `Report.from_json` keeps the checker's verdict, and
  routes as it did.

### Shims the engines share are proved once, as `Shim.*`

The lemmas for shims that several engines' translations write the same way
moved from `Polars.*` (and Spark's copies of them) to `Shim.*` in
`engines/Sverify/Engines/Shims.lean`: `one_zero` (`-0.0` as `0.0`), `null_order`,
`sum_empty_null`, `avg_trunc` (an integer `AVG` as the truncated mean) and
`makes_infinite` (#1166). DuckDB's, Polars's and Spark's rows cite them,
so `--options` and the realizability table name `Shim.one_zero` where they
named `Polars.one_zero` or `Spark.one_zero`.

### The analysis, a Lean package of its own

What `verify` proves of a plan under the core, the contract analysis, keys,
issues, sharding and guard elimination, moves into `analysis/`, the Lake
package `sverify-analysis` with modules `Sverify.Analysis.*`
([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
It builds on the core alone, with no engine in it, and CI checks that it
does. No theorem changed.

### Black boxes come from the engine package's catalogue

The reference's semantics no longer hold DuckDB's black boxes. A black box is a
row of a black-box catalogue (`Boxes`) that an engine package supplies, and the
core, `Rel.Allowed` and their theorems are parametric in it
([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
DuckDB's rows, their evaluators and the opaque functions behind them are in
`SubstraitLean/DuckDBBoxes.lean`, and the core holds no `opaque` black box.
A package that builds its own checker opens DuckDB's catalogue with
`open scoped Substrait.DuckDB` before calling `checkerMain`
(`SubstraitCheckExamples/DummyEngine.lean`). Verdicts do not change.

### The default engine is the plugin's

- Where no engine is named (`sv.connect()`, `Node.refresh()`, `sverify refresh`),
  plans run on the installed engine whose plugin is the default
  (`ProfilePlugin.default`: DuckDB), or else the first local one. With no engine
  installed, running a plan is an error that names what to install; `verify`
  needs no engine ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189),
  [#1288](https://github.com/AlexanderNenninger/substrait-lean/issues/1288)).
- An engine whose integer `//` and `%` floor says so in its plugin
  (`ProfilePlugin.floor_division`, Polars's); the Ibis producer and the division
  hints read it, where they named Polars before.

### An engine's name in prose

`ProfilePlugin` gains an optional `title`, the engine's name as prose and
the generated tables write it (`DuckDB`). The contract census, the coverage
table and the realizability page take their engines and names from the
installed plugins ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)),
so Spark's rows in `docs/realizability.md` now read "Spark".

### Every engine is a plugin

Sverify finds its engines in the entry-point group `sverify.profiles` and
nowhere else, its own among them: DuckDB, Polars, Spark, DataFusion and
Snowflake's dialect register a `ProfilePlugin` there, as a package from
outside does ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
`ProfilePlugin` gains optional fields for a runner (`runner`, `local`,
`optional`, `session`, `modules`, `read_settings`) and a SQL dialect
(`dialect`), so an engine from outside gets `connect`, `run` and `to_sql` as
the built-in ones have them. Entries for one engine merge field by field
([Engine profiles from outside](docs/engine-profiles.md#engine-profiles-from-outside)).
After upgrading an editable install, run `uv sync` so its metadata carries
the entry points.

### Engines-common, a Lean package of its own

What every engine shares moves into `engines/`, the Lake package
`sverify-engines` with modules `Sverify.Engines.*`: the Engine structure,
the table machinery (`EngineProfile`, the observation rows' constructors,
the option-wise transfer), the shared shims `Shim.*` and the
`check_generated` switch ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
It builds on the core alone, and CI checks that it does. No theorem
changed.

### Engines' function support and shims come from their plugins

- Which functions an engine runs, those it refuses with a reason of their own,
  the guards its dialect writes and what its shims do are the engine's plugin's
  (`ProfilePlugin.functions`, `window_functions`, `refuses`, `guards`,
  `shim_text`), no longer tables in sverify
  ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
- `sverify.engines.to_sql` takes a dialect by name: `to_sql(plan, "snowflake")`.
- Breaking: `sverify.engines.DUCKDB` and `SNOWFLAKE` are removed; name the
  dialect (`"duckdb"`, `"snowflake"`), or get its object with
  `sverify.sql.dialect_of`.

### sverify-polars installs without Polars

`sverify-polars` is the light layer of the Polars engine, as `sverify-spark`
is Spark's ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)):
its plugin and facts, enough to verify under `semantics="polars"`. Polars and
NumPy are its extra `run`, which `pip install sverify[polars]` installs as
before. A run without Polars says to install `sverify[polars]`.

### Profiles come from the installed plugins

- `verify(semantics=...)` takes the reference, DuckDB's semantics and every
  installed engine profile, as the plugins declare them:
  `sverify.profiles.ProfilePlugin.profile`, which defaults to whether the
  plugin brings a checker of its own, so a profile package from outside
  sverify keeps working unchanged. Substrait's own profile is a built-in
  plugin (`substrait`). `sverify.contracts.semantics_names()` lists what is
  installed ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
- `sverify.report.Semantics` and `sverify.engine.Engine` are now `str`, no
  longer `Literal` types that listed the built-in names.

### DuckDB is a package of its own: sverify-duckdb

sverify's DuckDB engine moves into the distribution `sverify-duckdb`
(`engines/duckdb/`, package `sverify_duckdb`), released with sverify at its
version ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
`pip install sverify` installs it with DuckDB, as before, and it registers its
`ProfilePlugin` in the entry-point group `sverify.profiles` as a package from
outside does. DuckDB's facts move to `engines/duckdb/facts/`, the replay of
its sqllogictests, the fuzz findings and the probes to `engines/duckdb/replay/`.

The DuckDB dialect module `sverify.sql.duckdb` is now `sverify_duckdb.dialect`
(`DUCKDB`); `"duckdb"` still names the default dialect.

For now `sverify` itself depends on `sverify-duckdb[run]` and on DuckDB: the
table store behind `sv.connect()` runs on DuckDB (`sverify_duckdb.DuckDBStore`). An engine-free base, with
every engine an extra (#1288), waits on a table store that does not need it.

### Polars is a package of its own: sverify-polars

sverify's Polars engine moves into the distribution `sverify-polars`
(`engines/polars/`, package `sverify_polars`), released with sverify at its
version ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
`pip install sverify[polars]` installs it, and with it Polars and NumPy, as
before. It registers its `ProfilePlugin` in the entry-point group
`sverify.profiles` as a package from outside does. Polars's facts and probes
move with it, to `engines/polars/facts/` and `engines/polars/probes/`.

`sverify.polars_engine` is now `sverify_polars.engine`, and
`sverify._polars_shims` is `sverify_polars.shims`.

`ProfilePlugin` gains three optional fields, so an engine package provides
what sverify asked of Polars by name before: `run_tables` (a run over Arrow
tables, which `sverify.engines.run_sharded` uses), `guard_free_theorem` (the
theorem behind a run without the checks a contract report discharged) and
`fallbacks` (the nodes a plan runs outside the engine's chosen executor,
which `streaming="require"` refuses).

### Spark is a package of its own: sverify-spark

sverify's Spark engine moves into the distribution `sverify-spark`
(`engines/spark/`, package `sverify_spark`), released with sverify at its
version ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
`pip install sverify[spark]` installs it with PySpark. It registers its
`ProfilePlugin` in the entry-point group `sverify.profiles` as a package from
outside does. Spark's facts, probes and fuzz findings move with it, to
`engines/spark/facts/` and `engines/spark/probes/`.

The Spark SQL dialect moves with the engine: `sverify.engines.SPARK` and
`sverify.engines.SPARK_CONF` are now `sverify_spark.dialect.SPARK` and
`sverify_spark.dialect.SPARK_CONF`, and `to_sql(plan, "spark")` needs
`sverify-spark` installed. `sverify.engines.run_spark`, deprecated since 0.5,
is gone: write `sverify.engines.run(con, plan, "spark")`, or pass your own
Spark session in place of `"spark"`.

### Calendar functions from 0001 to 9999 (D32)

- `date_part`, `date_trunc` to a week, month, quarter or year, `date_bin`,
  `strftime` and adding months work on every timestamp from 0001-01-01 to
  9999-12-31 on DuckDB, Polars and Spark. Truncations used to raise outside
  1677 to 2262, DataFusion's nanosecond range.
- A DATE or TIMESTAMP value lies in 0001 to 9999 by its type. Reading a
  table whose DATE or TIMESTAMP column holds a value outside it fails,
  naming the column, how many values and one of them. A computed date or
  timestamp outside it raises "outside the reference's timestamps" in a
  calendar function; a column read needs no guard or precondition.
- A `date_bin` origin outside 0001 to 9999 is refused when the plan is
  checked.

### A bound on `abs(x)` bounds `x`, and a `SUM` no longer depends on `avg_int_result`

A precondition `_.x.abs() < c` or `_.x.abs() <= c` on a double now bounds
`x` between `-c` and `c`, as `_.x.between(-c, c)` does, so a window or grouped
`SUM` or `AVG` of it raises no possible domain error. A call now reads only
the options of its group that apply to it (D34): a `SUM` no longer depends on
`avg_int_result`, which kept plans such as `h2o-groupby-q1` and `ssb-q1.1`
from transferring between profiles
([#1200](https://github.com/AlexanderNenninger/substrait-lean/pull/1200)).

### Window functions on Polars run natively

- Ranks, `NTILE`, `PERCENT_RANK`, `CUME_DIST`, frame aggregates and
  `FIRST_VALUE`, `LAST_VALUE`, `NTH_VALUE` run as Polars expressions on the
  streaming engine, with no Python in the window path. A running `SUM` over
  10⁵ rows takes 16 ms instead of 93 s
  ([#1269](https://github.com/AlexanderNenninger/substrait-lean/pull/1269)).
- A double `SUM` or `AVG` over a frame adds the frame's own values: a running
  sum for frames from the partition's first row, blocks of rows otherwise.
  The Polars profile's `window_sum_algo` is `RUNNING_ADD` and `TREE`, within
  the plan's bound as before (polars-window-agg). Polars's own
  `rolling_sum`, a sliding sum whose result is no sum of the frame, is not
  used.
- A `RANGE` frame with offsets over a date or timestamp key runs per
  partition; without `PARTITION BY`, its bounds take one in-memory step
  (`search_sorted`).

### `-0.0` as the engines compute it

- The reference computes doubles as IEEE 754 does, `-0.0` included:
  `0.0 * -1.0` is `-0.0`, and an `AVG` that underflows may be `-0.0`.
  Comparisons, `ORDER BY`, `DISTINCT`, `GROUP BY`, join keys and window
  partitions read `-0.0` as `0.0` and every NaN as the NaN, as DuckDB, Spark
  and Polars do ([core semantics](../docs/core-semantics.md)).
- A `DISTINCT` row, a `GROUP BY` key and a `MIN` or `MAX` may be any member
  of its class in the input, or the class's canonical value: a group of
  `-0.0`s may come out as `0.0`, as Spark and DuckDB give it. Plans whose
  keys and arguments hold no doubles keep one result.
- `x / -0.0` and `x % -0.0` raise as `x / 0.0` does. DuckDB's profile gives
  IEEE's signed `±∞` for them, and its `atan2` of signed zeros C's value.
- Substrait's `divide` with `on_division_by_zero: IEEE` on doubles is IEEE
  division: `1.0 / -0.0` is `-∞`. `0.0 / 0.0` and `∞ / ∞` raise in the
  reference, as every operation that would create a NaN does; DuckDB and
  Polars give NaN. The DuckDB SQL lift writes `/` of doubles this way under
  `semantics="duckdb"`, and Polars runs it natively.
- Which zero `round` and `ceil` give a negative value that rounds to zero is
  left open (`round_zero_sign`): DuckDB and Polars give `-0.0`, Spark `+0.0`,
  and the reference `0.0`. Results are compared up to the sign of a zero
  there.
- Incremental `GROUP BY`, `DISTINCT`, `MIN` and `MAX` keep one state row per
  class of keys, with its canonical key; Lean proves the maintained view is
  one the reference allows.
- `decode_double` gives `-0.0` for its code. Parquet statistics bound
  canonical values, so a file whose minimum is `0.0` still prunes correctly
  when it holds `-0.0`.

### Spark's profile is Spark's own

- Spark's profile states what Spark 4.3.0 computes under ANSI mode, from its
  [facts](../engines/spark/facts/): NaN where an operation creates one, NULL
  for a logarithm of `x ≤ 0`, no IEEE division, and the shift counts modulo
  64. It was the reference's
  ([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)).
- Until the checker reports under it
  ([#1288](https://github.com/AlexanderNenninger/substrait-lean/issues/1288)),
  `verify(semantics="spark")` gives the reference's report, with doubles that
  overflow allowed to be ±inf as before. `report.semantics` is `"reference"`,
  a `ProfilePendingWarning` says so, and the plan reaches Spark through its
  translation (route `translated`, before `native`).

### A plan that states `division_type: FLOOR` runs on every SQL engine

The SQL writer computes integer `//` and `%` with `division_type: FLOOR`
(the plans `semantics="polars"` writes) from truncating operations, as the
checker reads them (`Expr.floorDivOf`, `Expr.floorModOf`). DuckDB, Spark and
Snowflake no longer refuse such a plan before it runs: Spark's route proves
it again under `semantics="spark"` and runs it, and the written plan runs on
DuckDB with Polars's values. The route to DuckDB stays refused by the
transfer check, since the proof under Polars's profile does not carry over
to DuckDB's ([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

### Polars's variances keep a NaN

On Polars, a `VAR_*` or `STDDEV_*` of a group with a NaN returns NaN, as the
reference does. Polars's streaming `group_by` over a one-row frame gives 0
for a NaN (polars-var-pop-one-nan); sverify's plans did not take that path,
and now return NaN whichever path Polars takes (`_polars_shims.nan_through`).
The variance is aggregated once and clamped when it is read, so a plan
computes `var` or `std` once per measure, where it computed it nine times.

### Spark's variances lose DuckDB's NaN guard

The NaN guard on `VAR_*` and `STDDEV_*` (DD-3) is a dialect hook,
`Dialect.var_nan`, on by default. A dialect leaves it out where its engine's
profile states the `agg.var` `stat_algo` row without the shim: Spark's, whose
own variance of one NaN is NaN (spark-var-pop-one-nan). Spark's written SQL
drops one `COUNT` aggregate per variance and each copy of it, 30 % of the SQL
of a grouped variance. DuckDB and Snowflake keep the guard.

### Snowflake SQL, checked against a live Snowflake

Sverify's Snowflake SQL was run on Snowflake 10.40.102 (#63), and the writer
changes where it did not give the reference:

- A string's raise (`UPPER` or `LOWER` of non-ASCII text, `repeat` past
  2^31 bytes) returned its message as the value, since a cast to `VARCHAR`
  never fails. It now raises.
- `SUBSTR` reads positions and lengths as 32-bit integers: a start of
  2^32 - 1 picked the last character. Starts and lengths are clamped below
  2^31, and a start from 2^32 on raises as on the other engines.
- `VAR_*` and `STDDEV_*` of doubles are refused: Snowflake's give 0 for
  `1e9 + {4, 7, 13, 16}`, whose variance is 30.
- A modulus of doubles is refused: Snowflake's `MOD` computes
  `a - b * TRUNC(a / b)` in doubles, so `MOD(1e308, 9.13e10)` is 0 where the
  remainder is 3.8e10.
- Semi, anti and outer joins failed to compile (`002031 Unsupported subquery
  type`): a correlated `EXISTS` now has its condition bare in the `WHERE`.
- `strpos` is Snowflake's own `POSITION`, which gives 1 for an empty needle
  and NULL for NULLs, and integer arithmetic of literals folds when the SQL is
  written. The strings fixture's Snowflake SQL drops from 57 kB to 26 kB.

### Decimals on Spark

Decimal plans run on Spark (#27,
[#739](https://github.com/AlexanderNenninger/substrait-lean/issues/739)):
`+`, `-`, `×`, comparisons, casts, `SUM`, `MIN` and `MAX`, at the reference's
types and rounding.

- Spark's `-x` and `abs` round a decimal past 34 significant digits
  ([SP-1](upstream/bugs/SP-1.json)). The writer negates as `0 - x` there,
  exact up to 37 digits, or 38 at a scale of 6 or less, and refuses a
  `DECIMAL(38, s)` with `s > 6`; `Spark.decimal_negate_sub` proves the choice.
- A sum or product whose type would pass 38 digits at a scale above 6 is
  refused, since Spark would cut its scale. A double cast to a decimal past
  18 digits and an `AVG` of decimals are refused too, each naming the
  construct.
- `sverify.testing.decimal_literal` keeps every digit of a decimal wider
  than 28 digits; it used to round them.
- A routed run on Spark sends a table to the session once: a later run over
  the same table keeps its view.

### Spark as a profile

`verify(semantics="spark")` checks an Ibis transformation under Spark's
profile, and its plan runs on Spark by the route `native`, in `Report.run`
and in `Node.refresh(engine="spark")`
([#739](https://github.com/AlexanderNenninger/substrait-lean/issues/739)).

- Spark 4.3.0's choices, from its facts, are a table of the checker
  (`substrait-check --options`), so a plan verified under the reference
  reaches Spark with its class and the shims it needs named, and one verified
  under Spark's profile transfers to DuckDB where the choices allow it.
- The shims are proved in Lean (`SubstraitLean/SparkShims.lean`), with
  `Rel.spark_sound`: a verified plan, as `sverify_spark.dialect` writes it, gives
  the reference's rows on Spark under ANSI mode.
- A run reads the Spark session's settings and refuses one that changes
  what the profile relies on (ANSI mode, the timestamp type, the session
  time zone, …), naming the setting and how to restore it; another Spark
  version warns, another major version is refused.
- `MIN` and `MAX` of doubles run on Spark.
- Tables go to Spark as Arrow: a table of a million rows registers in a
  twentieth of the time, and no Python worker starts.

### A recomputed aggregate names its own reason

A node whose aggregate has no delta rules, such as an AVG of integers, said
it was recomputed because it was "not incrementally maintainable (left join,
fetch or window)", operators the plan need not contain. Its status now names
the measure: "mean is a AVG of int64: only integer SUMs and DECIMAL and
DOUBLE SUMs and AVGs are kept" (#742, #248). Views that are not aggregates
keep the checker's reason.

### The SQL lift refuses string casts DuckDB rejects

- `'_12.12'::DECIMAL(4,2)` and `'1e-9999999999'::DECIMAL` are refused by the
  SQL lift. DuckDB raises on them, and the lift used to fold them to `12.12`
  and `0.000` (#747).

### A windowed population variance of a lone NaN is NaN

`VAR_POP` and `STDDEV_POP` over a window frame whose only non-NULL value is
NaN gave `0.0` through the written SQL, where the reference (`varOf`) gives
NaN. DuckDB's population variance of one value is 0 whatever the value
([DD-3](upstream/bugs/DD-3.json), `duckdb-var-pop-one-value`). The SQL
writer already returned NaN for a group with a NaN; the window form now does
too ([#758](https://github.com/AlexanderNenninger/substrait-lean/issues/758)).

### Credentials by name, and the credentials each node uses

Pipelines name their credentials and hold no value (#774). A
`sverify.io.Secret` says where a secret lives: `env:NAME`, `file:/path`,
`bao:kv/path#field` (OpenBao, and `vault:` for Vault, with token or GitHub
Actions OIDC login), `aws-sm:`, `gcp-sm:`, `azure-kv:` and `keychain:`
(extras `secrets-aws`, `secrets-gcp`, `secrets-azure`, `secrets-keychain`),
or a bare name that `[tool.sverify.secrets]` in `pyproject.toml` (or the file
`SVERIFY_SECRETS` names) maps. `Storage(credentials=...)`, `Secret` option
values, `FlightSource(secret=...)`, `Lineage(api_key=Secret(...))` and
`credentials=` on `from_query`, `from_frame`, `from_files` and `sink_from`
take them; `SecretError` names the secret, never its value (#775).
`FlightSource(token=)` is deprecated.

`node.credentials()`, each refresh entry (`StageRefresh.credentials`, and
`"credentials"` in the refresh JSON) and `sverify check` list the
credentials each node uses, by name, for reading or writing. `Storage(reads=,
writes=)` or the configuration declare a credential's scope, and `sverify
check` warns about a table outside it (`[scope]`) and about options given as
values (`[inline_credentials]`) (#778). A test plants sentinel secrets in
every source and sink type and greps every output for them (#777).

A Delta source's refresh reads the table's log twice where it read it four
times: the table `latest()` opened serves the change and the file listing
of that version (on S3, 383 requests per refresh became 309 in the
benchmark of the PR).

### The pipeline template keeps stored keys to the store that needs them

The template's `lake.yml` passes a stored key to a job only when the store
has no OIDC federation (R2), and the Tailscale client's secret only for
MinIO; S3, GCS and Azure log in through OIDC with nothing stored (#776).
`docs/for-enterprise.md` gives each environment's role read grants on the
sources and write grants on its stage only (#778), and says how a source
token reaches a pipeline by name.

### OpenLineage

A refresh emits OpenLineage run events with `lineage=` (`sverify refresh
--lineage` on the command line), to a JSON lines file, the console, an
HTTP endpoint such as Marquez or DataHub, or any transport the OpenLineage
client's configuration names
([#792](https://github.com/AlexanderNenninger/substrait-lean/issues/792)).
Each node is a job and each refresh a run, with its inputs and outputs at
their versions, `schema`, `columnLineage` from the plan,
`dataQualityAssertions` for the conditions checked on data, and a
versioned `sverify_contract` facet with the contract, each
postcondition's status, the route, quarantined rows and the verified plan.
`sverify.openlineage.read` and `marquez` read upstream events: a
`sverify_contract` facet that sverify proves again becomes a downstream
transform's `requires`, and other tools' assertions are checked evidence.
Off by default. The new extra `sverify[openlineage]` installs the
OpenLineage client for its configuration.

### `sverify check --format junit` is removed

0.7.0's `junit` output is gone before 1.x freezes the command: JUnit XML has
no schema, only the conventions of each CI system that reads it. Use
`--format sarif` for code scanning, `--format github` for annotations on a
pull request, or `--format json` (`schemas/cli.schema.json`) for anything
else.

### Breaking changes: the formats' names for 1.0

The three formats take the names 1.x keeps, from the API review's section K
([api-review/PROPOSAL.md](api-review/PROPOSAL.md)). Each is now format 2,
and a reader maps what 0.x wrote
([docs/stability.md](docs/stability.md#the-formats)).

- The sink's contract record names the node `node` (`Contract.node`, for
  `Contract.view`). Delta keeps it under the commit key `sverify.contract`,
  as Iceberg does in its table properties. A Delta table written before
  keeps its records under `sverify`, which `DeltaSource.contract()` and a
  resuming `DeltaSink` still read.
- The Substrait manifest says `semantics`, `equivalence` and
  `equivalence_components` for `profile`, `observation` and
  `observation_components`, and `rows` is an integer. `sv.from_substrait`
  reads exports of format 1.
- The report's JSON says `semantics` in each route and `equivalence` in the
  report and each route. Postconditions, issues and assumptions take the
  shape of a SARIF 2.1.0 result
  ([#793](https://github.com/AlexanderNenninger/substrait-lean/issues/793)):
  `ruleId` (the code in snake_case: `may_be_false`, `division_by_zero`,
  `sum_overflow`), `level` (`error`, `warning`, `note` or `none`, for
  `error: bool`), `kind` (`pass` or `fail`), `message.text`, and sverify's
  fields under `properties`. One `ties` object holds the places and the keys
  that would close them, for `tie_places` and `ties`. Suggested
  preconditions are lists of `needed` objects, under `needs`, for
  `suggested`. The top-level `hints` and an issue's `expr` are gone: each
  issue keeps its `hint` and `shown`. `Report.from_json` refuses format 1,
  which no release wrote.

### Breaking: the engines, errors and environment variables of 1.x

From the API review before 1.0 (`api-review/PROPOSAL.md`, items 7, 8, 9 and
14).

Engines (A5, J3):

- `sverify.engine.Engine` is `"duckdb"`, `"polars"` or `"spark"`, the
  engines of the 1.x promise ([stability](docs/stability.md)), and
  `sverify.engines.ENGINES`, the engines a `Connection` runs plans on, is
  `("duckdb", "polars")`.
- The `iceberg` extra installs `pyiceberg[pyarrow,sql-sqlite]`, which a
  local SQLite catalog needs.

Errors and warnings (H1–H4):

- `sverify.errors.Unsupported` is `UnsupportedError`, and `NotIncremental`
  is `NotIncrementalError`. The old names, and `sverify.engines.Unsupported`,
  still work in this release with a `DeprecationWarning`:

  ```python
  from sverify.errors import UnsupportedError  # was: Unsupported

  try:
      sv.verify(query)
  except UnsupportedError as e:
      ...
  ```
- `SverifyWarning`, a `UserWarning`, is the base of every warning sverify
  issues: `filterwarnings("error", category=SverifyWarning)` fails a CI job
  on any of them. `@sv.transform(on_unproved="warn")` warns with an
  `UnprovedWarning`, and `on_inferred="warn"` with an `InferredWarning`
  (formerly `sverify.contracts.InferredPreconditionWarning`, which warns);
  each has the `.report`.
- Every `SverifyError` has a `code`, a snake_case string that names what
  failed and stays the same across 1.x: `not_proved`, `unsupported`,
  `precondition_failed`, `route_refused`, … ([`sverify.errors`](python/src/sverify/errors.py)).
- The API reference documents every error and warning, grouped by the proof,
  the data, running and setup.

Removed (M): the 0.6 aliases `transform(engine=)`, `transform(infer=)`,
`verify(infer=)`, `ContractedTransform.infer`, `Report.run(check_inputs=)`,
`Report.needs_text()`, `Report.needs_lines()`, `Node.plan`,
`route="reference"`, `to_sql(tie_free=)` and `run_spark(tie_free=)`.
`ContractedTransform` takes every argument after the function by keyword
(`@sv.transform` builds it).

Environment variables (J1, J2):

- `SVERIFY_CHECKER` is the path to a `substrait-check` binary, where it was
  `SVERIFY_CHECK`, which still works with a `DeprecationWarning`.
  `SVERIFY_PREBUILT_CHECKER` replaces `SVERIFY_PREBUILT_CHECK`, which is
  read too.
- `SVERIFY_TEMP_DIRECTORY` sets DuckDB's `temp_directory`, where it was
  `SVERIFY_SPILL_DIRECTORY` (0.6), which still works with a
  `DeprecationWarning`.
- The guide lists every variable with its flag and its Python keyword
  ([environment variables](docs/how-to-command-line.md#environment-variables)).

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
- `report.needed`, `report.needed_text`, `report.needed_conditions`,
  `Report.needs_text()` and `needs_lines()` warn: read `report.needs`, or
  `report.suggested_requires` for the whole mapping. The report JSON keeps
  its keys.

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

### The SQL lift reads VALUES, UNPIVOT and ASOF joins

Three relations of the 1.0 coverage targets
([docs/coverage-targets.md](docs/coverage-targets.md)) now lift from DuckDB
SQL and verify:

- `VALUES` in `FROM` and as a CTE, each column at the common type of its rows
  as DuckDB types it, named `col0`, `col1`, … without an alias
  ([#803](https://github.com/AlexanderNenninger/substrait-lean/issues/803)).
- `UNPIVOT [INCLUDE NULLS] (v FOR k IN (a, b AS 'x'))`, and the `UNNEST` of
  lists written out side by side (`unnest(['a', 'b']), unnest([a, b])`), as
  the `UNION ALL` they mean. Ibis's `pivot_longer` becomes the same union, so
  the catalogue's `dbt-unpivot-longer` verifies
  ([#804](https://github.com/AlexanderNenninger/substrait-lean/issues/804)).
- `ASOF [LEFT] JOIN` with `>=`, `>`, `<=` or `<`, written as
  `sverify.asof_join` writes it: a range join ranked by `ROW_NUMBER` per left
  row. Right rows that tie on the time leave the match to the engine, so the
  plan is reported as not deterministic
  ([#805](https://github.com/AlexanderNenninger/substrait-lean/issues/805)).

The lift no longer runs SQLGlot's type annotation, which nothing read, and
resolves each column type once: a lift takes a fifth less time.

Three fixes the replay of the new queries turned up:

- A RANGE frame's bounds overflow as in DuckDB: it computes `key ± offset`
  in an integer key's type and raises where a bound leaves it; the plan
  raises there too.
- A GROUP BY key that is the alias of a constant (`7 AS k … GROUPING SETS
  ((k), ())`) is that select column; the lift read the position `qualify`
  writes for it as the constant 1.
- `arg_min(x, y, n)` and `arg_max(x, y, n)`, which return lists of the `n`
  best, are refused; the lift dropped `n`.

### Spark and Snowflake run the RANGE frame guard

The guard the SQL lift writes on a `RANGE` frame with offsets over an integer
key, whose bounds DuckDB computes in the key's type
([#805](https://github.com/AlexanderNenninger/substrait-lean/issues/805)),
runs on Spark and Snowflake as well as DuckDB. Every such frame was refused
there. The date guards of `make_date` of columns
([#809](https://github.com/AlexanderNenninger/substrait-lean/issues/809))
stay DuckDB's, and their refusal says why: Spark's SQL of them exhausts its
JVM's heap, Snowflake's grows to 208 MB.

### Casts from VARCHAR, and TRY_CAST of strings

`CAST(s AS BIGINT)` (and the narrower integers), `DOUBLE`, `BOOLEAN`, `DATE`
and `TIMESTAMP` of a string column lift and verify, with DuckDB's rules:
spaces around, signs, fractions and exponents, `inf` and `nan`, the boolean
words, ISO dates and times
([#806](https://github.com/AlexanderNenninger/substrait-lean/issues/806),
[`duckdb-cast-varchar`](engines/duckdb/facts/duckdb-cast-varchar.json)).
`CAST` raises on a string DuckDB rejects, which `verify` reports as a domain
error; `TRY_CAST` is NULL there, so `TRY_CAST(value AS DOUBLE)` reads
numbers stored as text with flags such as `12.3 p` or `:` for missing. The
Ibis API's `cast` and `try_cast` of a string verify too. They are black
boxes that run on DuckDB; other engines refuse them until #271. A string
to a DECIMAL is still refused (#27).

### A DATE as a TIMESTAMP, and more temporal functions in SQL

The model casts a DATE to a TIMESTAMP, its midnight, and a timestamp to its
microseconds since 1970. So `CAST(d AS TIMESTAMP)`, `date_trunc` of a DATE
column and `DATE ± INTERVAL`, which DuckDB types as TIMESTAMPs, lift and
verify as output columns and in aggregates, and a DATE column compares with
a timestamp ([#807](https://github.com/AlexanderNenninger/substrait-lean/issues/807)).
The SQL lift reads `date_diff` in every unit from microseconds to years,
`epoch`, `extract(epoch …)`, `epoch_us`, `make_date`, `last_day`, `dayname`,
`monthname`, `isodow` and `isoyear`, and the Ibis API's `ibis.date` of
columns verifies
([#809](https://github.com/AlexanderNenninger/substrait-lean/issues/809)).
The new casts and `make_date` of columns run on DuckDB; other engines refuse
them until #271.

Writing a DATE's parts for DuckDB takes `date_part` of the date itself, three
times faster on 5,000,000 dates.

### The SQL lift reads regular expressions, padding and splitting

`sv.sql` queries and dbt models may use `regexp_matches`,
`regexp_full_match`, `regexp_extract`, `regexp_replace`, `right`, `lpad`,
`rpad`, `split_part`, `string_split(s, sep)[n]` and `concat_ws`, as the Ibis
API already could
([#808](https://github.com/AlexanderNenninger/substrait-lean/issues/808)).
`string_split` is a new black box, which Lean evaluates; like the other black
boxes, it runs on DuckDB and other engines refuse it until #271.

### Regular expressions in SQL: the operator `~` is refused

`s ~ p` and `s !~ p` are refused with a hint to write `regexp_matches(s, p)`:
DuckDB's `~` matches anywhere in the string, and SQLGlot reads it as
`regexp_full_match`
([SG-10](upstream/bugs/SG-10.json)). Patterns outside the supported subset
and `regexp_extract` groups past 9, where DuckDB raises, are refused when
the SQL is lifted
([#808](https://github.com/AlexanderNenninger/substrait-lean/issues/808)).

### The SQL lift reads ordered aggregates, IGNORE NULLS, interval frames and list functions

Six constructs of the 1.0 coverage targets
([docs/coverage-targets.md](docs/coverage-targets.md)) now lift from DuckDB
SQL, verify and run on DuckDB; other engines refuse the new functions
([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)):

- `string_agg(x, sep ORDER BY …)` (`listagg`, `group_concat`), `list(x ORDER
  BY …)` (`array_agg`), `bool_and`, `bool_or`, and `first`/`last` with
  `ORDER BY`. DuckDB's `list`, `first` and `last` keep NULLs, and so does the
  plan ([#810](https://github.com/AlexanderNenninger/substrait-lean/issues/810)).
- `first_value(x IGNORE NULLS)` and `last_value(x IGNORE NULLS)`, the last
  observation carried forward, and `RANGE` frames with an `INTERVAL` of days
  or less over a timestamp or a date
  ([#811](https://github.com/AlexanderNenninger/substrait-lean/issues/811)).
- `len`, `array_length`, `list_contains` (`list_has`), `list_position`,
  `list_concat` and lists of computed elements (`[qty, id]`), modelled in Lean
  as DuckDB 2.0 computes them
  ([#812](https://github.com/AlexanderNenninger/substrait-lean/issues/812)).

DuckDB's SQL for `first` and `last` (the Ibis producer's `first()`, `last()`
and `arg_min`) is DuckDB's own `first(x ORDER BY …) FILTER (WHERE x IS NOT
NULL)`, without gathering each group's values into a list: 4 times faster on
5 million rows.

`agg(x) EXPORT_STATE` is refused: SQLGlot reads `EXPORT_STATE` as the
aggregate's alias, and the lift took the value for the state
([SG-9](upstream/bugs/SG-9.json)).

### Snowflake SQL: time frames and set operations

Sverify's Snowflake SQL changes for two kinds of plan (Snowflake behaviour
recorded privately, #849):

- A `RANGE` frame with offsets over a timestamp (a rolling window of five
  minutes) orders by the key in microseconds since the epoch and takes the
  offset as that number, exactly.
- `INTERSECT` and `EXCEPT`, whose rows compare with NULL equal to NULL, write
  the comparison as Snowflake's `EQUAL_NULL`.

### Fixes

- Sverify's Snowflake SQL for a window `SUM` or `AVG` of doubles over a
  moving frame could give a value outside the plan's bound (Snowflake
  behaviour recorded privately). Such a frame's values are now collected
  (`ARRAY_AGG`) and added anew (`REDUCE`), within the plan's bound. Running
  and whole-partition sums keep Snowflake's `SUM`.

### DataFusion is no longer supported

Breaking: sverify no longer runs plans on DataFusion. The `datafusion` extra
is gone, so `pip install 'sverify[datafusion]'` fails; `engine="datafusion"`
raises "unknown engine"; and `sverify.engines.run_substrait_json`, the
checker's `--write-datafusion` and `ProfilePlugin.optional` are removed. Run
plans on DuckDB, Polars or Spark, or export them for any Substrait consumer
with `Report.to_substrait`. The DataFusion bugs sverify found stay recorded
in `upstream/bugs/DF-*.json`
([#868](https://github.com/AlexanderNenninger/substrait-lean/issues/868)).

### Breaking: a call's preconditions come back on its report

A contracted transform's call reports how it established each precondition
on a bound input (from the schema, from table metadata, or on the data) in
`Report.preconditions`, a list of `Discharged`, on the call's own report
(`transform.report`). A refresh reports its own in
`StageRefresh.preconditions`, as before
([#884](https://github.com/AlexanderNenninger/substrait-lean/issues/884)).

Moves:

- `ContractedTransform.last_preconditions`, deprecated since 0.6, is removed.
  Read `transform.report.preconditions`, or a refresh's
  `StageRefresh.preconditions`. The transform no longer keeps the last
  call's preconditions as state of its own, which a later call overwrote.

### Outputs keep credentials, data rows and stack traces to themselves

Sverify's outputs can go to CI artifacts, issues, a published catalog and a
lineage server, so three defaults changed (#887):

- Data rows are opt-in. `Refresh.to_json()` writes `"examples": []` for each
  quarantine entry unless called with `examples=True`, and
  `Refresh.alert()` gives counts, conditions and where the rows are, with
  the rows themselves only for `alert(rows=True)`. `sverify refresh` takes
  `--examples` for both. `PreconditionError.rows` and
  `QuarantineReport.examples` still hold the rows in the process.
- The OpenLineage FAIL event of a refresh that raised carries the
  exception's type, and its text only for sverify's own errors; the stack
  trace comes with `Lineage(trace=True)`. Before, every FAIL event carried
  the exception's text and the full trace.
- Every URI sverify records is written without userinfo, query string or
  fragment: a sink's `location`, `started`, `credentials[].location`, the
  ODCS `physicalName`, the OpenLineage namespace and `repr(Lineage)`. The
  user part of an Azure URI (`abfss://container@account...`), the
  container, stays. A URI that holds credentials in its userinfo counts
  as inline values, and `sverify check` warns `[inline_credentials]`.

The pipeline template's catalog publishes each table's contract record
without `cursors`, `table_ids` and `digests`, which only a resume reads.
`Source.restore` and `sink-contract.schema.json` say that a cursor is
stored in clear in the sink's table and must not be a credential.

### Observations have a meaning in Lean

Equality up to an observation is now a Lean relation, `Relation.Equiv`
(`core/Sverify/Core/ObsEquiv.lean`), and `Relation.Equiv_mono` proves that a finer
observation's equality implies a coarser one's, the order `Observation.refines`
computes (D18, #896). `substrait-check --options` reports each component's
levels and their order, and a test checks the Python order against it.

### Rewrites refine up to an observation

`Rel.Refines` was inclusion up to the order of rows, which let an unsorted
plan refine its `ORDER BY` twin. Refinement now names its observation,
`Rel.RefinesUpTo` (#897): `Rel.Refines` is exact and keeps the order an
`ORDER BY` fixes, and `Rel.RefinesBag` is the old relation. `optimize`'s
rewrites refine the plan up to the order of rows (`Rel.optimize_refines`).

### The checker says what a postcondition depends on

The checker now reports, for each postcondition, the components of an
observation its value depends on, from the columns it reads (#898).
`CheckedCondition.ignores` reads them, and Lean proves that a condition
depending on none of the components the observation ignores holds on every
result equal up to the observation (`Expr.robust_of_depends`). A comparison
narrowed by a tolerance is proved the same way (`Expr.narrow_sound`).

### Postconditions on every allowed result

`contract_sound_allowed` proves a postcondition on every result the
reference allows, every order and grouping of a double `SUM` or `AVG` among
them, where the plan reads no open sum to choose its rows (#899). The report
marks such a postcondition `CheckedCondition.allowed`: one on a plan without
open sums, or one that reads no open sum of an aggregate. Comparisons of the
open sums themselves follow with the tolerance's bound (#929).

### A verified contract holds on each engine's model, in Lean

- `Engine.contract_sound` proves that a contract verified under the reference
  holds on the rows the models of DuckDB, Polars, Spark and the reference
  compute for the translated plan, unless it raises
  ([#900](https://github.com/AlexanderNenninger/substrait-lean/issues/900)).
  Each engine's bridge, `Engine.Sound`, is a theorem (`SubstraitLean/EngineSound.lean`).
  The engine's actual output rests on the trusted claim `Engine.Runs` and the
  transfer check (`Engine.contract_sound_runs`). The check fails today at
  `sum_order`, `stat_algo`, `quantile_interp` and `zero_sign` on every engine,
  `null_order` without a preference on Polars and Spark, and integer overflow
  on Polars; the tolerance form for those is #900's PR 3.

### A faster contract check

The checker analyses each subplan once, bottom-up
([#903](https://github.com/AlexanderNenninger/substrait-lean/issues/903)).
Before, it walked a plan's inputs again at every filter and projection. On
the catalogue's contract requests `verify` spends about a fifth of the
checker time it did: the deepest join trees go from 1.0 s to 0.14 s, and a
chain of 40 projections from 0.34 s to 0.11 s. Results are unchanged:
`Rel.lane_eq` proves the one pass computes the same analysis.

### `SUM` and `AVG` of doubles are the exact sum rounded once (D25)

The reference's `SUM` of doubles is now the exact sum of the values rounded
once to the nearest double, and `AVG` the exact mean rounded once
([#915](https://github.com/AlexanderNenninger/substrait-lean/issues/915), epic
[#919](https://github.com/AlexanderNenninger/substrait-lean/issues/919)). It no
longer depends on the order of the rows, so a plan with double sums leaves the
engine no choice but the row order (`Rel.detPlan`), and its contracts hold of
every result the reference allows. Results can differ from 0.7 by an ulp: the
mean of three `0.1` is now `0.1`. Engines run as before, within the plan's
bound, which is now the engine's order plus half an ulp in place of twice the
order's bound, so `Report.epsilon` halves. A `GROUP BY` on the split key shards
a double `SUM` exactly, and `run_sharded` reports the larger of the two proved
tolerances of a split double sum.

### Engines run `SUM` and `AVG` of doubles natively

With the reference's correctly rounded sum (D25), no engine needs to add
doubles in Lean's order
([#917](https://github.com/AlexanderNenninger/substrait-lean/issues/917)).
DuckDB's SQL writes plain `SUM` where it emulated the order with
`list_reduce`, Spark's plain `SUM` where it sorted the values first, and
Snowflake and Spark no longer refuse a `SUM` or `AVG` of doubles, grouped or
not. Every engine's result is within the plan's bound of the reference
(`Report.epsilon`, `StdModel.epsilon_sum_cr`). A double `SUM` over 10⁷ rows on
DuckDB takes 0.02 s, down from 13.4 s. Windows over a Spark or Snowflake table
still need a proved `deterministic=True`, for their row order.

### CORR's missing bound says what would give one

`Report.epsilon` gives a `CORR` column no bound, as before; its reason now
states D30's decision: a bound needs a lower bound on both sides'
variances, stated by the user and checked by the run, and without one only
`[-1, 1]` holds and a tolerance on it is tested (#918). Polars's `VAR_*`
row cites a fuzzed bound of `1.03 · n·u·√(Q'S)` (`polars-var-bound`).

### DuckDB's variance NaN guard is proved

DuckDB gives `0.0` for `VAR_POP` and `STDDEV_POP` of a lone NaN
([DD-3](upstream/bugs/DD-3.json)), where the reference gives NaN. Sverify's
SQL has returned NaN there since #54 and #1141; the DuckDB profile now names
that guard as the shim `nan_through` of its `agg.var` `stat_algo` row, with
its soundness lemma `Stat.nanGuard_varStat` (#918). `--options` and the
realizability table list it as DuckDB's fourth shim.

### Incremental `SUM` and `AVG` of doubles, exactly

A view that ends in `SUM` or `AVG` of `DOUBLE` per group is now maintained
from an exact state (the count, the exact sum and the NaN and infinity
counts of each group) instead of recomputing the groups a batch touches. Its
value is the correctly rounded sum of the current rows after any sequence of
inserts and deletes, with no drift, which Lean proves
(`LinearAgg.fsum_no_drift`, #918). `LinearAgg.aggregate_maintained` now
covers any measure with a linear state, `COUNT` and `SUM` among them. A
`SUM` of `FLOAT`, or of doubles beside a `MIN` or `MAX`, still recomputes
the touched groups. A prototype on DuckDB (`python -m sverify_dev.ivm_float_sum`)
measures the drift a running double sum accumulates instead.

### Incremental `VAR`, `STDDEV`, `COVAR` and `CORR` of doubles, exactly

A view that ends in `VAR`, `STDDEV`, `COVAR` or `CORR` of `DOUBLE` per group
is now maintained from its exact moments (the count, `Σx`, `Σx²`, and for a
pair `Σy`, `Σxy`, `Σy²`) instead of recomputing the groups a batch touches.
Its value is D30's, the exact moments rounded once, after any sequence of
inserts and deletes, which Lean proves (`LinearAgg.no_drift`,
`varState_sound`, `covState_sound`, `corrState_sound`, #918).

### Bounds for statistical aggregates

- `Report.epsilon` gives `COVAR_SAMP` and `COVAR_POP` columns a bound, from
  the ranges of the pair's two sides, and marks a `VAR_*` or `COVAR_*`
  bound proved on the engines whose algorithm a theorem covers (DuckDB and
  Spark, `epsilon_var_cr` and `epsilon_cov_cr`; `"proved_on"`); on Polars it
  is tested. A `CORR` column has no bound, and says why (#918).
- Snowflake's `VAR_*` and `STDDEV_*` of doubles are written again, on values
  shifted by their group's mean ([#1023](https://github.com/AlexanderNenninger/substrait-lean/issues/1023)),
  where the plain formula cancels catastrophically. A `DISTINCT` one is
  still refused.

### `VAR`, `STDDEV`, `COVAR` and `CORR` are the exact moments rounded once (D30)

The reference's statistical aggregates of doubles are now one value each: the
exact moments of the values (`n`, `Σx`, `Σx²`, `Σxy`) rounded once
([#918](https://github.com/AlexanderNenninger/substrait-lean/issues/918)). They
no longer leave the engine a choice, so contracts over them hold of every
result the reference allows, and three axioms (`varOf_props`, `covOf_props`,
`corrOf_props`) are retired. Engines keep their own algorithms, within the
plan's bound: their rows are `approx`, `Report.epsilon` reports a bound for
variance and deviation columns, and the written SQL clamps a variance at `0`
and a correlation to `[-1, 1]`. Over a window, DuckDB runs its own `VAR_*` and
`STDDEV_*`, with no bound on the column yet (#1032). Results can differ by an
ulp from 0.7's.

### Values carry their kind

The Lean model's `Value` has a constructor per kind: integers, doubles,
dates, timestamps, times of day, decimals with their scale, strings, lists
and structs ([D29](docs/core-semantics.md#d29-a-value-has-its-kind),
[#923](https://github.com/AlexanderNenninger/substrait-lean/issues/923)).
A double no longer passes for an integer or a timestamp for a date: a
function of one kind gives NULL on another, comparisons take values of one
kind, and contracts track the kind of a column's numbers. `SUM` of decimals
of one scale is a decimal of that scale, whatever the order of the rows.

### A kind checker, and lambdas that read the row

The checker infers each column's kind and refuses a plan whose functions do
not fit their arguments (`+` of a double, a cast of a timestamp as a double),
with `well-kinded: no` and exit code 2. `Rel.kinds_sound` proves that a
well-kinded plan evaluates to values of its kinds, so the parser is no longer
trusted for typing ([#924](https://github.com/AlexanderNenninger/substrait-lean/issues/924)).

Lambdas have lexical scope ([D28](docs/core-semantics.md#d28-lambdas-have-lexical-scope)):
a body of `any_match`, `all_match`, `transform` or `filter` may read the
row's columns and an outer lambda's parameter. Plans that read only the
parameter keep their meaning; Polars still runs only those.

### Contracts on list and struct columns

The checker now describes a list column by its length and its elements, and
a struct column by its fields ([#925](https://github.com/AlexanderNenninger/substrait-lean/issues/925)).
Bounds and NOT NULL pass through `cardinality` (Ibis `length()`), `map`,
`filter`, list elements and `unnest`, so postconditions such as
`_.tags.length() <= 5`, NOT NULL elements after `map(lambda x:
x.fill_null(0))` or an element bound after `unnest` are proved. A
precondition on `length()` or a declared element type (`array<int64>`)
bounds the elements and lengths it starts from. The facts text names lists
("a list (length ≤ 5; of a string or NULL)"). Relations between the
elements of one list are not described (`docs/nested-values.md`).

### A LIMIT without an ORDER BY says how to fix its refresh

A `refresh` refuses a plan whose `LIMIT` has no `ORDER BY`, since a rerun may
take other rows, and the refusal now says to order the rows before the
`LIMIT` by a key ([#928](https://github.com/AlexanderNenninger/substrait-lean/issues/928)).
`verify` and `run` allow such a plan, and the proofs hold for every choice of
rows (`Rel.Bags`, `SubstraitLean/Seam.lean`). A route reads DuckDB's settings
in one query (0.86 ms to 0.25 ms).

### Double arithmetic is exact, rounded once (D31)

Sverify's reference now defines `+`, `−`, `×` and `÷` of doubles as the exact
result rounded once to binary64, to nearest with ties to even
([D31](docs/core-semantics.md#d31-double-arithmetic-is-exact-rounded-once),
[#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929)). No
result changes on an IEEE 754 engine. The eight trusted axioms about one
double operation (#582) are now theorems, so a contract over double
arithmetic rests on Lean's standard axioms. The checker computes these
operations on integers and checks them against native doubles on every
build.

### Contracts on double sums proved on Polars and Spark

- The route of a contract on a double `SUM` or `AVG` with a row cap
  (`sv.max_rows(n)`) now has evidence `proved` on Polars and Spark where its
  other rows are proved
  ([#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929)).
  Before, the engine's rounding of each addition rested on a probe. The plan's
  bound, `StdModel.epsilon_sum_cr`, holds whatever tie rule the engine rounds
  with. In the contract census, Spark's proved contracts go from 3 to 7 and
  Polars's from 1 to 4. DuckDB's stay tested on its `nan_creation` and
  `float_overflow` rows.
- Fixed: a shim no longer hides a plan's bound on doubles. DuckDB's `VAR`
  and `STDDEV` row shims NaN only (`nan_through`), yet a contract asking
  `sv.within(rel=1e-9)` of a variance whose bound is `abs = 1.78e-7` was
  accepted on DuckDB. It is now refused there, as on the other engines, with
  the tolerance that the bound does meet.

### Tolerance composition: double `SUM` and `AVG` summed over rows

- The `M₁` fold (`Rel.tol1`, `Rel.plan_nearL1`) now bounds a `SUM` or `AVG`
  of a tolerated double grouped by exact keys: the column's budget once, plus
  a cost per input row
  ([#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929)).
  Proofs only: no route or report changes.

### Thresholds on double sums run, checked on the data

- A filter on a double `SUM` or `AVG` against a constant (`HAVING SUM(amount) > 1000`),
  or on a row's value against its partition's window `SUM` or `AVG`
  (`value > AVG(value) OVER (PARTITION BY sensor)`),
  is no longer refused on DuckDB, Polars and Spark when no static bound
  decides it ([#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929)).
  The run first checks, per group, that the engine's sum is farther from the
  threshold than twice its bound, a bound from the group's count and
  `Σ|x|` (`StdModel.margin_check`). Then the engine keeps the reference's
  groups. A group that fails refuses the run with a `PreconditionError` that
  counts them; with `verify(on_inferred="warn")` the run warns, keeps them
  with the count in the warning. `on_inferred="off"`
  refuses the plan, as before.
- The check and the plan read their inputs twice, so the run requires one
  snapshot: an Arrow table, a table DuckDB holds, or a Delta or Iceberg table
  at one version. An input of another kind warns, and refuses the run with
  `reproducible=`.

### The margin check is proved in the core's doubles

- The margin check of a threshold on a double `SUM` or `AVG`
  ([#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929)) is
  proved against `Rel.AllowedP`'s sums and means in the core's own doubles
  (`MarginSound.lean`): a group the check passes has every sum or mean an
  engine's `sum_order` allows, and the reference's, on one side of the
  threshold. Its constants are defined once, as codes the check and the proof
  share. What stays trusted is that the check and the plan read the same rows
  from one snapshot, and that a group's `Σ|x|` stays below a quarter of the
  largest double.
- `AvgOrder.bound` gives an engine's double `AVG` a computable range (D35),
  as `SumOrder.bound` does for `SUM`.

### Tolerances compose along a plan

Sverify proves that a result within a tolerance of the reference in its double columns stays within a computed tolerance after each operator of a plan, and node after node in a pipeline (`Rel.plan_near`, `Rel.pipeline_near` in `SubstraitLean/Lipschitz.lean`, [#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929)). A filter, join key, group key or `DISTINCT` on a tolerated column has no such bound and is left out. `sverify.testing.allows_rows` indexes the choice rows on their fixed columns: 2,000 rows take 3 ms instead of 2.1 s.

### Double SUM and AVG bounds round once

The checker bounds a double `SUM` and `AVG` as D25 computes them, rounded
once: a mean of values in `[0, 100]` is in `[0, 100]`, with or without a row
cap, and a sum of at most `n` values in `[0, 100]` is in `[0, 100 n]`
([#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929)).
Exact postconditions such as `_.m.between(0, 100)` on an average are proved
where they needed `sv.approx` before, and casts of means need no row cap.

### A new connection no longer inherits a dead one's table facts

The metadata facts of a table read from a table format were kept by the
`id` of its connection's backend. Once that connection was gone, a new
connection could get the same `id` and take its facts for its own table of
the same name: a row-count fact then discharged a `rows_per` or `max_rows`
precondition the data broke
([#938](https://github.com/AlexanderNenninger/substrait-lean/pull/938)).
Each entry now holds a weak reference to its backend, and a dead backend's
entries are dropped.

### A sink's change lands only on the state it was computed from

When another commit of the same node reached a sink between two refreshes of
a process (a second process refreshing the same sink, or the late commit of
a crashed one after a restart resumed), the process wrote its change since
its own last state on top of that commit. On Delta a row that changed and
changed back stayed in the sink (#963). The process now writes its change
only on top of the record it wrote, skipped to or resumed from, and replaces
the rows otherwise. Found by the TLA+ model of the refresh protocol (#933).

### A sink commits only on the table version it read

A Delta or Iceberg sink's write was conditional on the value of the node's
epoch, which another plan's commit (a deploy) can repeat: a write prepared
against the old plan's rows then landed on the new plan's (#964). The write
now goes through the table `contract()` read, so Delta's conflict check and
Iceberg's snapshot assertion fail it on any commit of the node since, and
Iceberg's retry compares the node's last snapshot, not its epoch. Each write
opens the table once less. Found by the TLA+ model of the refresh protocol
(#933).

### A source that cannot restore is told apart by its contents

A `Source` without `restore` (`from_frame`, for one) numbers its versions by
the reads of the process. Its sinks now record a digest of its contents with
the version:

- A restarted job whose first read has the recorded digest resumes from
  the sink and writes nothing, where it rewrote the whole table on every
  run (#889).
- Two processes that numbered other contents alike no longer take each
  other's commit for their own state: the second numbers its version above
  the sink's and writes its rows (#965).

A node reading a `StaticSource` resumes from its sink after a restart too:
the check of the static tables' digests compared the stored ones with none.
Found by the TLA+ model of the refresh protocol (#933).

### A sink rewrites rows another application changed

When another application changed rows of a Delta or Iceberg sink after the
node's last commit, a restarted job already declined to resume from them,
but the write did not notice: it skipped the state as committed, keeping the
other rows under the node's record, or wrote its next change on top of them
(#966). A refresh now replaces the rows in that case; maintenance that keeps
the rows (compaction, vacuum, table properties) changes nothing. Found by the
TLA+ model of the refresh protocol (#933).

### Engine profiles from outside sverify

A package can add an engine profile without changing sverify: its Lean side
builds a checker over `builtinEngines` and its own `EngineProfile`, checked
by `#check_engine_profiles`, and its Python side registers a
`sverify.profiles.ProfilePlugin` under the entry-point group
`sverify.profiles`. Installed, `verify(semantics=<engine>)` and the routes
take it in, with its settings and version checks ([Engine profiles from
outside](docs/engine-profiles.md#engine-profiles-from-outside)).
`ProfilePluginWarning` reports an entry point that does not load.

### A tolerance on a double column without a bound is no longer reported met

A stated tolerance (`sv.equivalent(floats=sv.within(...))`) on a double
column whose bound the checker can't give, such as a `SUM` of doubles without
a row cap or a value computed from one, passed as met by every engine, and
the plan reported proved. It is now refused there with the reason
(`… has no bound on its distance to the reference …`), and a run on such a
column counts as tested, not proved.

### Fixes

- On Polars, a window `SUM` or `AVG` whose frame holds both `+inf` and `-inf`
  is NaN again, as in the reference and on DuckDB; a merge had made it raise a
  domain error.

## 0.7.1 (2026-11-07)

Two soundness fixes on 0.7.0. Every plan 0.7.0 ran still runs.

### Fixes

- A stated tolerance (`sv.equivalent(floats=sv.within(...))`) on a double
  column whose bound the checker can't give, such as a `SUM` of doubles
  without a row cap or a value computed from one, passed as met by every
  engine, and the plan reported proved. It is now refused there with the
  reason (`… has no bound on its distance to the reference …`), and a run on
  such a column counts as tested ([#1029](https://github.com/AlexanderNenninger/substrait-lean/pull/1029)).
- A window `SUM`, `AVG`, `VARIANCE` or `STDDEV` of doubles was classed
  `exact`: the plan's bound left window functions out
  ([#1032](https://github.com/AlexanderNenninger/substrait-lean/issues/1032)).
  Such a plan still runs. `Report.epsilon` gives the column no bound
  (`"abs": null`, naming #1032), its route is observed on tested evidence,
  and a tolerance stated on the column is refused.

## 0.7.0 (2026-11-05)

0.6.0 was tagged but never published: two tests the release ran against the
installed wheel read repository files the wheel doesn't have, so nothing
reached PyPI. 0.7.0 is the first release of 0.6.0's changes (the 0.6.0
section below), of 0.5.0's, and of these. It is also the first release of
`sverify-dbt`, at the same version. A release's version-bump pull request now
runs the whole wheel test, so a failure like this shows before the tag.

### Breaking changes

Upgrading from 0.4.0, read the 0.6.0 and 0.5.0 sections' breaking changes
too. New in 0.7.0, in the entry "Breaking: sources, sinks and the top level of
1.x" below:

- `StaticSource(table, name=...)` and `sverify.testing.source(..., name=...)`
  need `name=`, and `version` is keyword-only.
- `SourceBatch.kind`, `SourceRefresh.mode` and `SinkWrite.mode` are
  snake_case (`"change_feed"`, `"snapshot_diff"`, `"row_level"`), with no
  deprecation period.
- Renamed keywords and methods on sources and sinks warn and name the new
  form.
- SQL from `node.to_sql(dialect)` and `report.to_sql(dialect)`; one way to
  run on Spark (`sverify.engines.run`); `con.create`, `con.rows`, `con.get`
  and `con.put` replace the table helpers; `substrait_json` lifts under the
  reference semantics by default.
- The `sverify` command's exit codes, flags (`check --fix/--diff/--full`,
  `--format`) and JSON (format 1 of `schemas/cli.schema.json`) change before
  1.x freezes them.

Names deprecated in 0.6.0 and 0.7.0 still work with a `DeprecationWarning`
that names the replacement; they go in 0.8, since 0.6.0 never reached PyPI.

### Coverage targets for 1.0

`docs/coverage-targets.md` lists the SQL and Ibis constructs sverify 1.0 covers, by area, with the ones skipped and the reason for each ([#743](https://github.com/AlexanderNenninger/substrait-lean/issues/743)). `python -m sverify_dev.coverage --targets` prints the share covered, 27 of 60 on 2026-11-05.

### A template repository for pipelines on GitHub

- `templates/pipelines/` holds the contents of a template repository for
  data engineering on your phone
  ([#771](https://github.com/AlexanderNenninger/substrait-lean/issues/771)):
  workflows that prove each pull request's pipelines and comment the
  contract in plain words (`check`), run them on staging data with a
  preview catalog (`preview`), refresh `main`'s on a schedule in a
  `production` environment (`refresh`), publish a catalog to GitHub Pages
  with DuckDB-WASM (`pages`) and open an issue when a refresh fails
  (`alerts`). Tables go to a `data` branch by default, or to your bucket
  through OIDC for enterprise. A worked pipeline keeps Eurostat's
  `nama_10_gdp` up to date, and `CLAUDE.md` with sverify's skills teaches
  Claude Code the loop. CI runs the template's steps on a recorded Eurostat
  response against every change to sverify.

### ODCS contracts

`sverify.odcs` writes a node's contract as an Open Data Contract Standard
document (ODCS v3.2.0) and reads ODCS contracts as conditions
([#791](https://github.com/AlexanderNenninger/substrait-lean/issues/791)).
The export maps NOT NULL columns to `required`, keys to `primaryKey` and
`unique`, value sets, ranges and row caps to quality rules, and the
docstring to descriptions; each rule carries a `sverify` custom property
saying whether it is proved, checked on the data or declared. `odcs.read`
gives the conditions for `requires` or `ensures` and lists, with a warning,
every rule it cannot read. `sverify contract export <file>:<node> --format
odcs` writes it from the command line. YAML needs the new extra
`sverify[odcs]`.

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

### Repeated terms written once

A term a written plan computes in several places, `CASE` branches among
them, is now computed once as a column when the plan evaluates it on every
row anyway (#821, `Expr.repeated` in `SubstraitLean/Bind.lean`). Ibis's
`find` with a start drops from 66 kB of Snowflake SQL to 3 kB, and
`day_of_week.full_name()` from 11 kB to 2 kB on DuckDB and Spark.

### Smaller written SQL

Sverify binds the arguments that its guards would copy to columns before it
writes a plan (`SubstraitLean/Bind.lean`, #821): a nested date or double
operation, or an aggregate's argument, is computed once in a projection
below and read by name. The `month end` query of #821 drops from 51 kB of
Spark SQL to 7 kB, and the catalogue's largest Snowflake statement from
547 kB to 16 kB. `Rel.evalI_bindArgs` and `Rel.raises_bindArgs` prove
that the plan computes the same rows and raises the same errors on every
engine.

### Breaking: SQL from a node or a report, one way to run on Spark, `Connection` methods (api-review F1 to F4)

From the API review before 1.0
([#795](https://github.com/AlexanderNenninger/substrait-lean/pull/795),
`api-review/PROPOSAL.md` F1 to F4). The deprecated names still work in
0.7 with a `DeprecationWarning` that names the replacement, and go in 0.8.

- `node.to_sql(dialect)` and `report.to_sql(dialect)` write the plan a proof
  checked as DuckDB, Snowflake or Spark SQL (`"duckdb"`, `"snowflake"`,
  `"spark"`, or a `Dialect`), with its run-time checks. They refuse a plan
  that is not proved (`UnverifiedRunError`), as `refresh` and `run` do, and a
  report's `deterministic` lets windows run without a row-order tiebreak.
  Before, the way to SQL was `to_sql(json.loads(node.internal_plan), dialect)`.
- `con.create(name, schema, rows)` and `con.rows(name)` replace
  `sverify.engines.create_table(con, name, schema, rows)` and
  `table_rows(con, name)`, which warn.
- `Connection.arrow` and `Connection.ibis` are deprecated: `con.get(name)`,
  `con.rows(name)` and `con.put(name, table)` read and write the tables, and
  `con.table(name).get_backend()` is the Ibis backend, for SQL of your own.
- `sverify.engines.run(con, plan, "spark")`, or a Spark session as the
  engine, is the one way to run a plan on Spark; `run_spark(plan, tables)`
  warns. A window without a row order runs on Spark when the contract
  states its order key (`sv.unique(...)`), through `node.to_sql("spark")`
  or `report.to_sql("spark")`; `run` takes no tie flag.
- `sverify.engines.substrait_json(con, sql)` now lifts the SQL under the
  reference semantics, as `sv.verify` and `sv.sql` do. Pass
  `semantics="duckdb"` for what DuckDB computes, the old default.
- The API reference documents `Dialect` by its fields (`name`, `guards`,
  `finite`, `decimals`). Its SQL-writing methods, subclasses of it, and the
  plan layer (`to_sql`, `substrait_json`, `written_plan`,
  `run_substrait_json`, `delta_plans`) are outside the 1.x promise
  ([docs/stability.md](docs/stability.md)).

Migration:

```python
# before
from sverify.engines import SNOWFLAKE, create_table, run_spark, table_rows, to_sql
create_table(con, "orders", schema, rows)
table_rows(con, "orders")
to_sql(json.loads(node.internal_plan), SNOWFLAKE)
run_spark(plan, {"orders": orders_table})
con.ibis.raw_sql("SELECT 1")

# after
con.create("orders", schema, rows)
con.rows("orders")
node.to_sql("snowflake")
run(con, plan, "spark")  # con holds the orders table
con.table("orders").get_backend().raw_sql("SELECT 1")
```

### `round(x, d)` follows DuckDB 2.0 where the result overflows

`round(x, d)` with a negative `d` gives `x` itself where the rounded value
would overflow, as DuckDB 2.0 does (`round(1.5e308, -308)` is `1.5e308`),
where the model gave 0, DuckDB 1.4's answer. The Polars and SQL writers
follow, and the engine fact `duckdb-round-digits-2` supersedes
`duckdb-R15-round-digits`, whose probes missed the case.

### Faster rows in and out of a connection

`con.create`, `con.rows` and the row lists a refresh reads build and read
Arrow tables column by column, without a dictionary per row: 100,000 rows of
four columns go into a table in 22 ms (88 ms before) and out in 71 ms (92 ms
before), with a quarter and three fifths of the Python memory.

### Breaking: the `sverify` command before 1.0 (API review I1–I5)

The command 0.6.0 shipped (#744) changes its exit codes, flags and JSON
before 1.x freezes them
([#797](https://github.com/AlexanderNenninger/substrait-lean/pull/797)):

- Exit codes: 0 proved (a refresh committed every row), 1 not proved,
  2 usage error (argparse's too), 3 unsupported or refused, 4 time or
  memory budget exceeded, 5 a refresh quarantined rows or held a node,
  6 error. In 0.6.0, 2 was refused, 3 budget, 4 error. `sverify --help`
  lists them.
- `sverify suggest <file> [--apply]` is `sverify check <file> --diff` (show)
  and `--fix` (write, then check again).
- `sverify explain <file>:<node>` is `sverify check <file>:<node> --full`;
  `explain` takes codes only.
- Codes are snake case (`may_be_false`), as the report writes them, each with
  a level; `explain` still reads kebab case.
- `--format text|json|github|sarif|junit` (`--output-format`; `--json` is
  `--format json`). `github` writes workflow commands that annotate a pull
  request's lines, `sarif` a SARIF 2.1.0 log for code scanning, `junit` a
  test report
  ([#793](https://github.com/AlexanderNenninger/substrait-lean/issues/793)).
- The JSON is format 1 of `schemas/cli.schema.json`: each node's `name`,
  `nodes`, `status`, `summary` (its third key is `not_proved`), `links` and
  `report`, the node's `Report.to_json()`. The 0.6.0 keys `verdict`,
  `problems`, `needs` and `facts` come from the embedded report.
- `sverify contract export` (#791) follows the same exit codes.
- `import sverify` loads its names on first use: `sverify --help`,
  `--version` and `explain` take 0.1 s, down from 1.3 s.

### The checker's slow cases

- The checker's abstract evaluation no longer evaluates a projection's or an
  aggregate's input once per expression, which grew exponentially with the
  plan's depth: TPC-DS q36 took 56 s per proof and takes 0.8 s, and the
  catalogue's 55 contracts 110 s and 5 s
  ([#825](https://github.com/AlexanderNenninger/substrait-lean/issues/825)).
  A decimal cast's bounds, each table's description and a plan with
  `VALUES` cost less too.

### A faster check: a proof cache, and no search where only ties are open

- Sverify keeps the checker's answers on disk, so the next `verify`,
  `check` or `refresh` of an unchanged transform does not prove it again.
  An entry is keyed by the plans, conditions and profile the checker reads,
  sverify's version and a hash of the checker binary; any change to them
  proves again. The cache is in `SVERIFY_CACHE_DIR` (default
  `~/.cache/sverify`), and `SVERIFY_CACHE=off` turns it off
  ([#825](https://github.com/AlexanderNenninger/substrait-lean/issues/825)).
- A postcondition that only the order of ties leaves open has the reason
  `"ties"` (`CheckedCondition.ties`), and the counterexample search skips
  it ([#691](https://github.com/AlexanderNenninger/substrait-lean/issues/691)).
- A checker request interrupted by the CLI's time budget or Ctrl-C ends
  the checker's process. Before, its answer stayed in the pipe and the next
  request read it as its own.
- The checker speaks protocol 2 (a `--rows` mode for the counterexample
  search): rebuild a checker you set with `SVERIFY_CHECK`.
- CI times every catalogue transform and the tour's notebooks, cold and
  warm, by stage, and fails past the budgets of
  [#745](https://github.com/AlexanderNenninger/substrait-lean/issues/745)
  (`python -m sverify_dev.bench`).

## 0.6.0 (2026-11-05, tagged, not published)

0.5.0 was tagged but never published: a Spark test ran out of memory in the
release's wheel tests, so nothing reached PyPI. 0.6.0 is the first release of
0.5.0's changes (the 0.5.0 section below) and of these. It is also the first
release of `sverify-dbt`, at the same version.

### Breaking changes

Upgrading from 0.4.0, read the 0.5.0 section's breaking changes too. New in
0.6.0, each with its own entry below:

- Fewer knobs for "not proved" and one name per concept (#690, #695):
  `on_inferred="off"` replaces `infer=False`; the route `"reference"` is
  `"translated"`; `@sv.transform(engine=)` is `check_engine=`;
  `Report.run(check_inputs=)` is `check_requires=`; `node.plan` is
  `node.internal_plan`. Renamed keywords warn and go in 0.7. Removed:
  `strict=`, the positional `sv.references`, `Connection.datafusion`.
- A run of an unproved plan raises `UnverifiedRunError`, a
  `VerificationError` and a `RouteError`.
- Every exception sverify raises derives from `sverify.errors.SverifyError`.

### Quarantine: bad rows set aside, the rest flows

A batch that breaks a precondition on a source no longer has to stop the
pipeline ([#184](https://github.com/AlexanderNenninger/substrait-lean/issues/184)).
`on_violation` on `sv.transform` or on a source chooses what a refresh does:

- `"quarantine"` sets the offending rows aside, with the reason, in a table
  next to the node's sink (`<sink>_quarantine`, or `.write(sink,
  quarantine=...)`), and the node runs on the others. A row breaks a row
  condition, or shares its key with another row: every row of a repeated
  key is set aside, so the rule needs no order and a recompute agrees with
  the batches. `Catalog.kept_sound` (`SubstraitLean/Quarantine.lean`)
  proves every precondition holds on the kept rows, so the node's proof
  holds. A delete or update upstream releases rows.
- `"hold"` commits nothing for the batch and holds the node at its
  versions until a later version meets the preconditions. Conditions on a
  table as a whole (`max_rows`, `arrives_within`) hold the node this way
  under quarantine too.
- `"error"` stays the default.

The refresh report says how many rows each refresh set aside, released and
saw deleted, with examples. `Refresh.outcome` (`"ok"`, `"quarantined"`,
`"held"`), `Refresh.alert()` (Markdown for whoever is on call) and
`Refresh.to_json()` (format 1, `sverify/schemas/refresh.schema.json`) are
new, and `Node.quarantined()` returns the rows set aside. `sverify refresh`
exits 5 when rows are quarantined or a node is held, with `status`
`"quarantined"` or `"held"` in its JSON. The quarantine
table's format is stable within 1.x (`sverify/schemas/quarantine.schema.json`,
[docs/stability.md](docs/stability.md)).

`SchemaError` now names the column, the change, the version and the
contract it breaks, with what to do: "`orders.id` became nullable at v12,
and the new rows have NULLs in it; `paid` requires _.id.notnull(). Fix the
upstream, or handle NULLs in `paid` (e.g. `.fill_null(0)`) and relax
`requires`."

### One vocabulary for `on_unproved`, `on_inferred` and `on_violation`

The three `on_*` parameters share their values (the API review's C1): `"error"`
raises, `"warn"` goes on with a warning, `"ignore"` goes on silently,
`"check"` checks on the data at run time, `"off"` infers nothing, and
`on_violation` adds `"quarantine"` and `"hold"`.

- `on_unproved="runtime"` is now `on_unproved="check"`, and
  `on_inferred="silent"` is `on_inferred="ignore"`. The old spellings still
  work for one release, with a `DeprecationWarning`; a report JSON written
  with `"silent"` reads as `"ignore"`.
- `transform(check_requires=False)` with an `on_violation` other than
  `"error"` raises `ValueError`: that setting acts on the checks it turns off.

### Breaking: fewer knobs for "not proved", one name per concept (#690, #695)

From the API critique (#686). Every renamed or removed keyword below still
works in 0.6 with a `DeprecationWarning` that names its replacement, and goes
in 0.7. The names deprecated before 0.5 are gone.

Not proved (#690):

- `on_inferred="off"` replaces `infer=False` on `sv.verify` and
  `@sv.transform`: nothing is inferred or assumed, so a `SUM` that may leave
  64 bits, or a double operation that may overflow to ±inf, is an error.
  `on_inferred` takes `"error"` (the default), `"warn"`, `"silent"` and
  `"off"`. `infer=` warns.
- `@sv.transform(on_unproved="warn")` now lets the node's refreshes run
  unverified, each with an `UnverifiedRunWarning`, where it used to need
  `refresh(unverified=True)` as well.
- A run or refresh of a plan that is not proved raises
  `sverify.errors.UnverifiedRunError`, a `VerificationError`, so
  `except VerificationError` catches every "not proved". It is also a
  `RouteError`, so `except RouteError` still catches it. A refresh's message
  names `refresh(unverified=True)`.
- An assumed `SUM` reads `fits 64 bits in every group (checked at run time:
  the job raises if it does not; on_inferred="off" makes it an error)`, and
  an assumed finite double operation `stays finite on finite inputs (checked
  at run time …)`. Neither says "inferred" any more.
- Removed: `@sv.transform(strict=...)` (deprecated since 0.4),
  `sv.references(col, table, other)` (write `to=`), and
  `sverify.testing.Connection.datafusion` (deprecated since 0.4).
- `node.plan` is `node.internal_plan`: sverify's own form of the plan, with
  its private extension URNs. `Report.to_substrait()` is the portable one.
  `node.plan` warns.

Names (#695):

- The route `"reference"` is `"translated"`: a plan verified under
  `semantics="reference"` runs through the translation to the engine.
  `route="reference"` warns and takes `"translated"`; `Route.kind` is
  `"translated"`.
- A route's line names the route only where it is not `translated`:
  `exact; transfer: verified under semantics="duckdb"; …`.
- Printed output says `semantics="duckdb"` where it said `Profile.duckdb`.
- `@sv.transform(engine=)` is `check_engine=`: where checks on data run.
  `refresh(engine=)` and `run(con, engine)` keep `engine` for where the plan
  runs.
- `Report.run(check_inputs=)` is `check_requires=`, as on `@sv.transform`.
- `sverify.engines.to_sql(tie_free=)` is `deterministic=`, as on
  `Report.run`; `run_spark` too. `to_sql` also takes the plan as a JSON
  string, so `to_sql(node.internal_plan, SNOWFLAKE)` needs no `json.loads`.
- `Node.refresh(engine=None)` and `Group.refresh` default to `None`, DuckDB,
  as `Report.run(engine=None)` defaults to its connection's engine.
- `sv.verify`'s first parameter is `query`, positional-only.
- `report.equivalence` is the equivalence the result is proved up to, by the
  name of `sv.equivalent`; `report.observation` stays.
- `report.needed_text` is a property; `Report.needs_text()` and
  `needs_lines()` warn.
- A refresh report of a stored node is headed by the transform and the sink,
  `daily_revenue → daily:`, where the names differ.
- `summary()` reads `changes from orders v1→v2 (change feed)` where it read
  `orders@v1→v2, Δ trusted (change feed)`.

### Public API additions

- `sverify.__version__` is the installed version, and `dir(sverify)` lists
  `__all__` and `__version__`; the submodules import as before.
- `node.to_substrait()` and `transform.to_substrait()` export the report of
  a node and of a transform's last call, as `report.to_substrait()` does;
  `node.report` is that report.
- `PreconditionError` carries the table (`.source`), the condition
  (`.condition`) and up to ten of the rows that break it as an Arrow table
  (`.rows`).
- `sv.key("id")` states a primary key: `sv.unique("id")` and
  `'"id" IS NOT NULL'`.
- `report.not_null` lists the output columns the checker shows are never NULL, and
  a stored node writes them as NOT NULL columns and records them in its
  contract, with those `ensures` states.
- `report.needed_conditions` gives `report.needs` as conditions ready for
  `requires=`: Ibis deferreds for an Ibis transform, SQL strings for a SQL
  one.
- Every exception sverify raises on purpose derives from
  `sverify.errors.SverifyError`, and keeps its built-in base; the classes
  stay importable where they are defined.
- `isin([0, 1])`, and SQL's `x IN (0, 1)`, of integers that fill a range is
  read as that range, so a column known to lie in it meets the condition.

([#691](https://github.com/AlexanderNenninger/substrait-lean/issues/691))

### The strings a column can hold

Sverify tracks the strings a column can be while they are few (up to 64):
a constant is its string, `s = 'k'` and `s IN ('a', 'b')` narrow a column,
`s <> 'k'` and `NOT IN` take strings out, and `CASE`, `COALESCE`, projections,
joins, grouping and `UNION ALL` carry the sets through. A filter
`status <> 'cancelled'` over a source whose `status` is one of four strings
proves `status IN ('placed', 'shipped', 'returned')`, which is dbt's
`accepted_values`, and a tag that is a constant in each branch of a
`UNION ALL` proves the tag's values. The report's facts name the strings:
"one of the strings 'q1', 'q2', 'q3', 'q4'"
([#708](https://github.com/AlexanderNenninger/substrait-lean/issues/708)).

A key of each branch of a `UNION ALL`, with a column the branches cannot share
a value in (a constant tag, a `GROUPING` level, ranges apart), is a key of the
union. `unique(region, quarter)` over an unpivot by `UNION ALL`, and the
group keys of a rollup written as a union, now prove
([#436](https://github.com/AlexanderNenninger/substrait-lean/issues/436)).

### sverify-dbt lives in this repository and is released with sverify

`sverify-dbt` ([`dbt/`](dbt/README.md)), which proves a DuckDB dbt
project's data tests and model contracts before the models run, is back in
this repository with its history. From this release on it is published to
PyPI with sverify, at the same version, pinning `sverify==<version>`. The
`dbt` CI job runs its tests, its check of the sample project
(`dbt/examples/shop`, 19 of 26 tests and constraints proved), and
`dbt build` without the proved tests
([#732](https://github.com/AlexanderNenninger/substrait-lean/issues/732),
[#177](https://github.com/AlexanderNenninger/substrait-lean/issues/177)).

### A map of the proofs

[`docs/proofs.md`](docs/proofs.md) names each Lean module's job and the
theorems each guarantee rests on (`contract_sound`, `Rel.keys_sound`, the
delta rules, the engine profiles' shims), with what they trust. Each
generated Lean module's header says how to regenerate it, and
`tests/test_proof_map.py` keeps the map in step with the modules (#733).

### Stable formats and a stability policy for 1.x

[docs/stability.md](docs/stability.md) states what 1.x keeps stable: the
formats a running pipeline reads, the contracts it proved, and the Python
API, which breaks in a minor release only loudly, with a test, a changelog
entry and a migration note
([#737](https://github.com/AlexanderNenninger/substrait-lean/issues/737)).

- The sink's contract record (`sverify.io.Contract`) has a `format`, 1, and
  a JSON schema, `sverify/schemas/sink-contract.schema.json`. A record
  without `format`, written before this release, reads as format 1; a
  record of a newer format is refused with an error that says to upgrade
  ([#734](https://github.com/AlexanderNenninger/substrait-lean/issues/734)).
- The Substrait contract metadata, `io.sverify.substrait.v1.Contract`,
  follows protobuf's rules for updating a message, and its manifest has a
  JSON schema, `sverify/schemas/substrait-manifest.schema.json`
  ([#735](https://github.com/AlexanderNenninger/substrait-lean/issues/735)).
- `python/tests/formats/` holds what each release wrote: Delta and Iceberg
  sinks from 0.4.0 on and Substrait exports.
  [`tests/test_formats.py`](python/tests/test_formats.py) reads them all, and
  a pipeline resumes from an old Delta sink.

### The report as JSON

`Report.to_json()` writes a report as a versioned JSON document for CI jobs
and tools, and `Report.from_json()` reads it back into a `Report` with the
same verdict
([#736](https://github.com/AlexanderNenninger/substrait-lean/issues/736)).
The document holds the verdict, each postcondition with its reason, message
and counterexample, the runtime issues and assumptions, what the proof needs
(`Report.needs`), the facts, the non-NULL columns and the routes. Its format
is 1, with a JSON schema, `sverify/schemas/report.schema.json`, and follows
the rules of [docs/stability.md](docs/stability.md): within 1.x it only gains
keys, and a reader refuses a newer format with an error that says to
upgrade. `python/tests/formats/` holds reports for
[`tests/test_formats.py`](python/tests/test_formats.py) to read back.

### The `sverify` command

- `sverify check <file>[:<node>]` proves every contracted transform and node
  a Python file applies, without running it, and prints the contract in
  plain words first: what the output guarantees, what each refresh checks
  on the data, and what is not proved, each problem with a code. A dbt
  project goes to `sverify-dbt check`
  ([#744](https://github.com/AlexanderNenninger/substrait-lean/issues/744)).
- `sverify suggest <file> [--apply]` writes the preconditions the proofs
  need (`Report.needs`) into the decorators' `requires=`, then checks the
  file again.
- `sverify refresh <file>:<node>` runs a node and reports what changed;
  `sverify explain <code>` explains a code, and `sverify explain
  <file>:<node>` prints a node's full report.
- Every command takes `--json` (a provisional format until #736) and exits
  0 proved, 1 not proved, 2 refused, 3 budget exceeded, 4 error.
- `--timeout` (default 30 s, `SVERIFY_TIMEOUT`, 0 turns it off) bounds
  proof, planning and checking, never a refresh moving data.
  `--memory-limit` (`SVERIFY_MEMORY_LIMIT`) sets DuckDB's `memory_limit`,
  with a spill directory (`SVERIFY_SPILL_DIRECTORY`); a breach stops before
  any sink commits.
- `sverify.cli.discover(path)` does what `check` does from Python.

### Spark's local session keeps its parser cache bounded

`sverify.engines`' local Spark session turns on Spark's management of the SQL
parser's ANTLR cache (`spark.sql.parser.manageParserCaches`, flushed at 10 % of
the driver heap). The deeply nested SQL that sverify writes for date arithmetic
grew that cache to most of the 1 GB default heap, and later queries failed with
`AGGREGATE_OUT_OF_MEMORY` (the 0.5.0 Wheels run). `SVERIFY_MEMORY_LIMIT`
(#783) now also sets the session's `spark.driver.memory`.

## 0.5.0 (2026-11-05, tagged, not published)

### Breaking changes

Upgrading from 0.4.0, check these first. Each has its own entry below.

- `Report.run`, `Node.refresh` and a group's `refresh` refuse a plan whose
  report is not proved (#655). Pass `unverified=True` to run it anyway. Runs
  choose their route by default (`route="auto"`); `route=None` is gone.
- A precondition that sverify infers is an error by default (#655): add it to
  `requires`, or pass `on_inferred="warn"` (0.4.0's behaviour, with a
  warning) or `on_inferred="silent"`.
- Route classes are renamed (#655): `refines` is `exact`, and
  `refines_up_to` and `approx` are `observed`. The other two classes are
  `shim` and `refused`.
- A sink's `reproducible` defaults to doubles within the plan's proved bound
  (`floats="plan"`) (#655). A sink whose consumers need the same bits on a
  rerun states `reproducible=sv.equivalent()`.
- `Report.run` checks preconditions and the absence of new `±∞` on the data
  before it runs (#604, #575). A batch that breaks them is refused with a
  `PreconditionError`. `check_inputs=False` skips the precondition check.
- `AND` and `OR` evaluate both operands (#604, D19), so an error in either
  operand counts. A constant subexpression that raises makes the whole plan
  raise (#609). Both change the reference.
- Polars always runs on its streaming engine. Polars's engine settings and
  environment variables no longer choose the engine.
- The SQL lift refuses rankings with an `ORDER BY` of their own (#625).
- The reference leaves the order of ties open (#679, D24). Proofs hold for
  every order. A deterministic run (`deterministic=True`, an incremental
  refresh, or a sink's `reproducible=`) refuses a plan whose ties stay open,
  and names each place (`Report.tie_places`).
- `verify` checks a stated float tolerance against the plan's bound on each
  engine (#689). A tolerance tighter than every engine meets leaves the plan
  unproved; before, it was refused only at run time.

### `sv.rows_per` bounds the rows per key, and row caps bound exact sums

`sv.rows_per(["customer"], at_most=n)` in `requires` states that at most `n`
rows of an input agree on the columns. It is checked on the data like
`unique`. Lean carries the bounds through filters, sorts, `DISTINCT`,
projections, unions and joins on a key, and an aggregate grouping by the
columns has groups of at most `n` rows. So an integer or decimal `SUM` of
values in `[-m, m]` per group is proved to fit when `n · m` does, without a
cap on the whole table
([#219](https://github.com/AlexanderNenninger/substrait-lean/issues/219)).
`Report.relations` lists the bounds on each relation's rows.

A row cap (`sv.max_rows`) now also bounds the value of an exact `SUM`, so
decimal arithmetic on a sum, such as TPC-H q11's `SUM(…) * 0.0001`, can be
proved to fit
([#470](https://github.com/AlexanderNenninger/substrait-lean/issues/470)).

### Sharded integer AVG

`--shard` and `sverify.engines.run_sharded` split an integer `AVG` (Substrait's
`avg` of `i64` with an `i64` result) across shards: each shard computes a `SUM`
and a `COUNT`, the combining plan adds them up and divides, truncating toward
zero. Lean proves it once for algebraic aggregates, a final expression over
distributive partials (`Rel.eval_algebraic` in `SubstraitLean/Partition.lean`),
when the plan's column types make the argument an integer. `AVG` with a double
result is still refused with `float_order="exact"` ([#245](https://github.com/AlexanderNenninger/substrait-lean/issues/245)).

### COUNT, SUM and DISTINCT are maintained from changes

A node that ends in an aggregate of `COUNT` and integer `SUM` per group, or
in `DISTINCT`, is now maintained from the changes to its input when the
input has delta rules. It keeps a count and a sum per group beside its rows
and adds each batch's change to them, so a refresh no longer reads the input
of the groups a batch touches, and `status()` reports the node as
maintained. Lean proves the result equal to a full recompute, groups that
appear and disappear included (`LinearAgg.aggregate_maintained` and
`LinearAgg.distinct_maintained`). An integer `SUM` that leaves 64 bits still
raises, as on a full recompute. This is the first stage of
[#248](https://github.com/AlexanderNenninger/substrait-lean/issues/248).

### MIN, MAX, exact AVG, semi and anti joins are maintained from changes

A node that ends in `MIN`, `MAX`, or a `DECIMAL` `SUM` or `AVG` per group is
now maintained from its input's changes, like `COUNT` and integer `SUM`. A
batch that only inserts into a group merges its values into the group's
state; the groups it deletes from are recomputed from the new input, and
only those. A node that ends in a semi or anti join on equal keys keeps a
count of matches per key, so a refresh never reads the right side and reads
the left side only for the keys that gain their first match or lose their
last. Lean proves each equal to a full recompute
(`ExtremeAgg.extreme_maintained`, `ExtremeAgg.map_maintained`,
`SemiDelta.semi_maintained`), and the new state survives a failed commit.
`mean()` of integers, a double, is still recomputed by touched groups. This
is the second stage of
[#248](https://github.com/AlexanderNenninger/substrait-lean/issues/248).

### Polars runs decimal plans

`engine="polars"` runs plans over `DECIMAL` columns, which it used to refuse
("unsupported column type"). Values keep the plan's `DECIMAL(p, s)`, and the
translation computes what Polars rounds differently: a product at the sum of
the scales, a smaller scale and an `AVG` half away from zero, an empty `SUM`
as NULL ([#27](https://github.com/AlexanderNenninger/substrait-lean/issues/27),
[engine-profiles.md](docs/engine-profiles.md#decimals-on-polars)). The 22
TPC-H queries, 8 TPC-DS queries and 10 finance queries of the catalogue now
run on Polars. A cast of a double to a decimal of more than 22 places is
refused there.

### `verify` reports a decimal `SUM` that may leave its precision

A `SUM` of decimals has a declared precision: ten more digits than its
argument, at most 38. DuckDB raises past it ("Overflow in SUM of DECIMAL"),
while `verify` let a contract over the sum be proved. It now reports the
overflow as it does an integer `SUM` that may leave 64 bits: with `infer`,
the sum is assumed to fit and checked on the data while the job runs
(`Report.assumed`), and row caps with a bound on the column prove it fits
([#316](https://github.com/AlexanderNenninger/substrait-lean/issues/316)).

### Black-box functions

DuckDB functions the checker treats as opaque now come from one table,
`core/Sverify/Core/BlackBox.lean` ([#325](https://github.com/AlexanderNenninger/substrait-lean/issues/325)).
Each row gives a function's types, how it treats NULL, whether it may raise,
and its laws, which the contract checker uses and Lean proves of the model.
The SQL lift reads them, the plan calls them under the URN
`extension:io.sverify:black_box`, and DuckDB runs its own function; other
engines refuse them (#271). The first two are `base64(encode(s))` (also
`to_base64`), never NULL for a string, and the aggregate `entropy(x)`, a
double at least 0, so `verify` proves `entropy(x) >= 0`. Adding a function is
adding a row ([reference semantics](docs/reference-semantics.md#black-boxes)).

### Statistical aggregates as black boxes

The SQL lift reads more of DuckDB's aggregates as black boxes
([#326](https://github.com/AlexanderNenninger/substrait-lean/issues/326)):
`product`, `kahan_sum` (also `fsum`, `sumkahan`), `favg`, `sem` and `mad`, not
NULL over values, `sem` and `mad` at least 0; and `kurtosis`, `kurtosis_pop`
and `skewness`, which DuckDB raises on for infinite or huge values, so
`verify` reports a domain error. Black-box aggregates may now raise. Integers
are converted to doubles, as DuckDB converts them. `bit_count` of a BIGINT is
exact, in [0, 64]. `histogram` (a MAP) and `weighted_avg` (two arguments) are
refused with a reason. The engine facts `duckdb-moments` and
`duckdb-statistical-aggregates` record what DuckDB 2.0.0 does.

### Vector and list functions

The SQL lift reads DuckDB's vector functions of lists of doubles as black
boxes ([#327](https://github.com/AlexanderNenninger/substrait-lean/issues/327)):
`list_cosine_similarity`, at least -1, so `verify` proves
`array_cosine_similarity(a, b) >= -1`; `list_cosine_distance` and
`list_distance`, at least 0; `list_inner_product`,
`list_negative_inner_product` and `array_cross_product`. Each may raise, on a
NULL element or lists of different lengths. The `array_*` names are read as
the functions of lists. `list_sum` of integers is exact, a BIGINT as `SUM`'s.
`list_extract`, `list_element` and `array_extract` are read as `l[i]`, and
`array_value(…)` as a list literal. The engine facts `duckdb-list-vectors` and
`duckdb-list-sum` record what DuckDB 2.0.0 does.

### More DuckDB scalars as black boxes

The SQL lift reads more of DuckDB's scalars
([#328](https://github.com/AlexanderNenninger/substrait-lean/issues/328)),
as rows of the black-box table: `printf` and `format` of a format and one
value, which may raise; `octet_length(encode(s))` and `strlen(s)`, the UTF-8
byte length, at least 0; `signbit` of a double; and `yearweek` of a date,
bounded by DuckDB's dates. Lean evaluates all but `printf` and `format`.
`weekday(d)` is now read as `dayofweek(d)`, exactly. `age` stays refused:
its INTERVAL is not in the model. The engine facts `duckdb-printf`,
`duckdb-signbit` and `duckdb-yearweek` record what DuckDB 2.0.0 does
([reference semantics](docs/reference-semantics.md#black-boxes)).

### A SUM of a double constant is a double SUM in the written SQL

The SQL writer read a double constant in an aggregate as an integer, as Lean's
`Expr.kind` does for a double's code, where Lean's parser goes by the plan's
literal. So `SUM('inf'::DOUBLE)` was written as an integer `SUM` and raised
"integer overflow in SUM: inf", where `Rel.eval` and DuckDB give `inf`. The
writer now reads the declared type as Lean does (`doubleJ`), for `SUM`, `AVG`
and the sides of `COVAR_*` and `CORR`
([#341](https://github.com/AlexanderNenninger/substrait-lean/issues/341)).

### Hash joins and hash aggregation in Lean's evaluator

`substrait-check` evaluates plans with inlined data through `Rel.evalFast`
(`SubstraitLean/EvalFast.lean`), which Lean proves equal to `Rel.eval`, rows and
order included (`Rel.evalFast_eq`). Equi-joins, semi-joins, `EXCEPT` and `INTERSECT` hash the right
side, and `DISTINCT`, `fn(DISTINCT …)` and `GROUP BY` use hash sets and maps,
where `Rel.eval` compares every pair of rows. The query of DuckDB's
`hash_join_dict_surviving_outer_build.test` (3,532 rows) evaluates in 0.41 s,
down from 9.2 s, and its larger variant in 0.33 s, down from 54 s.
`substrait-check --eval-spec` evaluates with `Rel.eval`, for tests
([#357](https://github.com/AlexanderNenninger/substrait-lean/issues/357)).

### Proved error bounds for sharded double `SUM` and `AVG`

`--shard` and `sverify.engines.run_sharded` with `float_order="any"` now split
`SUM` and `AVG` of doubles with a proved bound on how far each result is from
Lean's one-pass sum. Each shard also reports `SUM(|x|)`, `COUNT(x)` and
`MAX(|x|)` per split double, `--shard`'s output says which columns carry the
bound (`float_bounds`, `Split.float_bounds`), and `run_sharded(...,
tolerance=True)` returns a `Sharded` with τ per row and column.
`sverify.partition.apriori_tolerance` gives the bound before running, from a
row cap and a bound on the values. The bounds are proved in
`float-bounds/FloatBounds/Shard.lean` and linked to the split plan by
`floatSplit_sum` and `floatSplit_avg` in `SubstraitLean/Partition.lean`
([#428](https://github.com/AlexanderNenninger/substrait-lean/issues/428)).

### The SQL lift reads the variance family

`sv.sql` and SQL transformations now lift `STDDEV_SAMP`, `STDDEV_POP`,
`VAR_SAMP`, `VAR_POP`, the aliases `STDDEV` and `VARIANCE`, `COVAR_SAMP`,
`COVAR_POP` and `CORR`, of integers and doubles, to the Substrait functions the
Ibis producer writes. With `semantics="duckdb"`, `CORR` is DuckDB's: NaN for
one pair or a side whose values are all equal, where the reference's is NULL
(`duckdb-corr`). The SQL writer now runs a `FILTER` on `COVAR_*` and `CORR`. Sverify proves what it proves for Ibis's `std()`, so
`SELECT workflow, stddev_samp(duration_s) FROM jobs GROUP BY workflow` gives
"a double ≥ 0.0 or NULL", with `GROUP BY ROLLUP` too. Of a `DECIMAL` they are
refused for now
([#433](https://github.com/AlexanderNenninger/substrait-lean/issues/433)).

### `verify` proves that a `SUM` of a 0/1 flag fits 64 bits

Counting rows with `SUM(CASE WHEN … THEN 1 ELSE 0 END)` no longer gets a
"SUM overflow" warning. A group has fewer than 2⁶³ rows, as `COUNT(*)` is a
BIGINT in the reference and in every engine, so a `SUM` of values in
`[-1, 1]` fits 64 bits without a row cap. The size hypothesis of the
reference semantics now states that bound. Values in a wider range still
need `sv.max_rows(n)` to be proved
([#437](https://github.com/AlexanderNenninger/substrait-lean/issues/437)).

### Ibis conditions on SQL transformations

`sv.verify` on a SQL string took only SQL conditions and raised a
`TypeError` on an Ibis one. Its `ensures` and `requires` now take Ibis
conditions too: an Ibis postcondition reads the lifted query's output, and
an Ibis precondition its input table, so a query keeps its contract when it
moves between SQL and Ibis
([#438](https://github.com/AlexanderNenninger/substrait-lean/issues/438)).

### DeltaSink accepts its constraints as Delta stores them

Delta (delta-rs) reads a CHECK constraint back in its own form: `x BETWEEN 0 AND 10` as `x >= 0 AND x <= 10`, and `hi >= lo` as `lo <= hi`. `DeltaSink` now compares constraints after rewriting `BETWEEN` into its two comparisons and turning every comparison to face the same way, so a stored node with a proved `between` or a column-to-column comparison in its `ensures` refreshes again after its first write ([#439](https://github.com/AlexanderNenninger/substrait-lean/issues/439), [#487](https://github.com/AlexanderNenninger/substrait-lean/issues/487)).

### The options a plan meets, and whether its proof transfers

`substrait-check --dependencies <plan.json>` lists the options a plan meets,
with the reference's, DuckDB's and Polars's choice at each. It says, for each
pair of profiles, whether a proof under the first holds under the second, and
which shims each engine needs for the plan. Lean proves the check sound
(`Rel.transfer_of_transferB`,
[#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

### Engine settings checked before a routed run (#444)

A profile's facts hold under the engine's default settings. Before
`Report.run(..., route=...)` or `refresh(route=...)` runs, sverify reads
the settings the plan will run under and compares them with those the
facts were probed under. A setting a choice depends on refuses the run
with the setting named (`sverify.errors.EngineSettingsError`): on DuckDB
`default_null_order`, `default_order`, `integer_division`,
`error_on_division_by_zero`, `ieee_floating_point_ops`,
`default_collation`, `scalar_subquery_error_on_multiple_rows`,
`enable_optimizer` and `disabled_optimizers`; on Polars an engine
affinity that forces another engine than streaming
(`pl.Config.set_engine_affinity("in-memory")`), since sverify runs
Polars's streaming engine (#605). DuckDB's
`preserve_insertion_order` warns (`EngineSettingsWarning`). `TimeZone` and
`Calendar` are not checked: the written SQL never reads them
(duckdb-time-zones). DuckDB's settings are read on the cursor sverify
runs plans on, so a `SET GLOBAL`, or a `SET` of a global-only setting, is
seen; a session's `SET` on another cursor is not.

### DuckDB and Polars as choice tables

`substrait-check --options` now prints DuckDB's (2.0.0) and Polars's (2.1.0)
choices and how each relates to the reference, option by option, for integer
and double arithmetic, `SUM`, `AVG` and sorts, from their facts in
`characterization/`
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).
A plan's integer `divide` may now state `division_type: TRUNCATE`, which is
what it computes.

### The float tolerance per engine

`--contract` now gives each double output column a bound per engine
(`"epsilon_by_engine"`). The bound carries the summation order's share and
each engine's own per-operation error through `+ − × /` from the ranges the
preconditions give: Polars's division by a literal is within 3u of IEEE's
quotient, and its `log10`, `log2` and `log(b)` within 2.1 ulp; DuckDB's
`log(b, x)` within 1.4 ulp; `+ − × /` and `sqrt` are correctly rounded on
both. Lean does not prove these bounds yet
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

### Engine sums, transfers up to an order, and a LIMIT over ties

- DuckDB's and Polars's double `SUM` and `AVG` are within #85's bound of the
  reference's, not one of its orders: DuckDB merges partial sums in finishing
  order and adds a constant vector as one product; Polars's in-memory groups
  use Kahan's sum
  ([#633](https://github.com/AlexanderNenninger/substrait-lean/issues/633)).
- The transfer check between profiles (`--transfer`, a route's transfer)
  accepts a behaviour below the one the proof used, such as a sequential sum
  where the proof allowed any order.
- A contract's dependency report leaves out the value choices of columns
  nothing reads.
- A `LIMIT` below an `ORDER BY` that ties, or with none, makes the report
  not deterministic
  ([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444), D10).

### The reference's options in one table

The options a plan may set, and the reference's choice at each, are now one
table in Lean (`core/Sverify/Core/Options.lean`, step 1a of
[#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)), and
the parser reads it. `substrait-check --options` prints it. Plans are read as
before, with one addition: `variance` and `std_dev` of integers accept
`rounding: TIE_TO_EVEN`, as `avg` of integers does.

### Polars plans stream, with native expressions

The Polars engine now computes integer `POWER`, month arithmetic and
`date_trunc` of dates, `GREATEST` and `LEAST`, double sort, group and join
keys, and the aggregates `COUNT`, `MIN`, `MAX`, `BIT_AND`, `BIT_OR`,
`BIT_XOR`, `VARIANCE`, `STDDEV` and their `DISTINCT` forms as Polars
expressions, where it ran Python and numpy on each batch before, so these
plans run fully on Polars's streaming engine. A test checks every plan the
Polars tests run: a node on the in-memory engine fails it unless
`polars_engine.ALLOWED_FALLBACKS` lists it (`ARRAY_AGG`'s ordered list,
window frames). `Report.run(..., streaming="require")` refuses a plan with
such a node, and a routed run records them in `Route.fallbacks`.

Double `/` is Polars's own: by a constant it goes through the reciprocal and
is within 2 ulps (PL-3, from #608), and a subnormal divisor is refused on the
data. numpy, imported only when needed, keeps `%` of doubles (C's `fmod`)
and `ROUND(x, d)`'s division by `10^d` exact. `power(-inf, 0.5)` is `+inf`
and a difference of zeros the one zero, where Polars gives NaN and `-0.0`
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

### Plans checked under Polars's semantics run natively on Polars

`verify(semantics="polars")` now checks an Ibis transformation under
`Profile.polars`, an evaluable profile in Lean
(`SubstraitLean/PolarsProfile.lean`): integer `//` and `%` floor, as Polars's
do, so a postcondition such as `x % 2 >= 0` is proved. The plan states
`division_type: FLOOR`, the checker reads it as Polars's remainder (proved on
64-bit integers), and `report.run(con, "polars", route="auto")` takes the
`native` route, with no shim. DuckDB and the other engines refuse such a plan
with the reason. `substrait-check --contract` answers `"profile": "polars"`,
so the re-check route can target Polars, and inferred preconditions work
under `semantics="polars"`
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

### The Polars shims, proved (#444)

Each shim and guard of the translation from the reference to Polars
(`sverify._polars_shims`) now has a Lean theorem of its name,
`Polars.<name>` in `SubstraitLean/PolarsShims.lean`: the shimmed expression
gives the reference's value, and each guard flags exactly where the
reference's precondition fails. `Polars.written_faithful` and
`Rel.polars_sound` prove the error-side rows need no shim for a verified
plan. `substrait-check --options` reports these rows as `"evidence":
"proved"` with the theorem and the facts its model rests on.

### Polars runs the reference natively, with named shims

The Polars engine now runs integer `+`, `-`, `*`, division and remainder, and
`SUM` and `AVG` of a group as Polars's own operations. Where Polars 2.1.0
gives another value than the reference on inputs the reference does not raise
on, a named shim (`sverify._polars_shims.SHIMS`) gives the reference's:
truncating division and remainder, `ROUND`'s halves away from zero, `NULL` for
an empty `SUM`, the integer `AVG` in its declared type, one zero, each sort
key's NULL placement and stable ties. Each shim names the Polars fact it rests
on ([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

A double `SUM` or `AVG` now adds in Polars's own order, which the reference
allows (`sum_order = ANY`), so its last bits may differ from `Rel.eval`'s. A
sort key without a direction sorts ascending with NULLs last. `guards=` of
`run` and `to_lazy` also takes the issues to check by name, such as
`{"SUM overflow", "overflow to infinity"}` for the preconditions a report
assumes ([#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575)).

### Polars runs every query on the streaming engine

Sverify now runs each Polars query on Polars's streaming engine, named
explicitly, so `POLARS_ENGINE_AFFINITY`, `pl.Config.set_engine_affinity`,
`POLARS_FORCE_STREAMING` and `POLARS_AUTO_STREAMING` no longer choose the
engine. A Polars `LazyFrame` given as a source is collected the same way.
Operators the streaming engine lacks still run on the in-memory engine inside
the streaming plan; `sverify.polars_engine.streaming_fallbacks` lists them
for a query
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

### Proved float tolerances for `SUM` and `AVG`

The per-plan tolerance `--contract` reports for a double `SUM` or `AVG`
(`"epsilon"`) is now proved in Lean for every summation order the engines
use: trees of additions, DuckDB's constant runs and Polars's Kahan sum
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444),
[#85](https://github.com/AlexanderNenninger/substrait-lean/issues/85)). So is
the relative bound for values of one sign, and the propagation of `ε` through
`+`, `-`, `*` and `/` per engine
([#568](https://github.com/AlexanderNenninger/substrait-lean/issues/568)).
Routes that rest on these bounds report evidence `proved` where they reported
`tested`; elementary functions and `Float32` sums stay `tested`
([docs/float-bounds.md](docs/float-bounds.md#the-engines-orders-and-epsilon-444)).

### The realizability table (#444)

`docs/realizability.md` lists, for DuckDB and Polars and every option of
the catalogue, how a plan verified under the reference runs there: native,
after a shim (with its cost), up to an observation, within a float bound,
behind a precondition the reference raises on, or refused, with the theorem
or facts each row rests on, and the shim count per engine. It is generated
from `substrait-check --realizability` (`SubstraitLean/Obligations.lean`)
by `python -m sverify_dev.realizability --write`, and
`tests/test_realizability.py` checks it is current. `Rel.duckdb_refines`
states DuckDB's translation as a refinement of the reference, raise sets
included (`Lowering.lowerRel_raises`). `substrait-check --dependencies` and the
route's class list the Polars `null_order` shim only where a key leaves its
NULL placement unspecified.

### Routes and determinism in refreshes (#444)

- `Node.refresh(engine=..., route="auto")` and `sv.group(...).refresh(route=...)`
  take each node's proof to the engine by a route, as `Report.run` does,
  and refuse before anything runs where none applies
  (`sverify.errors.RouteError`). `StageRefresh.route` records the route and
  its class.
- A stored node whose result is not determined up to row order (its
  report's `deterministic`) is refused: its sink commits each epoch once,
  so a rerun must give the same rows (D10 of
  [core-semantics.md](docs/core-semantics.md#d10-determinism)). A node
  without a sink reports it.

### What a rerun must reproduce (#444, D20)

Each output now has two observations: the postcondition's
(`sv.equivalent` in `ensures`), and what a rerun must reproduce, which
the result's consumer states. Sinks take `reproducible=sv.equivalent(...)`
(`DeltaSink`, `IcebergSink` and custom sinks through `Sink.__init__`), with
rows as a multiset and exact values by default, since a sink commits each
epoch once. `refresh(reproducible=...)` and
`Report.run(..., route=..., reproducible=...)` state one for a run; a plain
run requires none and reports determinism. The engine's run-to-run
variation on the options the plan depends on (the `rerun` column of its
choices; for Polars's streaming float `SUM`, within the plan's bound) must
refine it, and a result not determined up to row order fails every
requirement. Otherwise the refresh or run is refused with the reason
(`RouteError`). `deterministic=True` asks for exact values. Where the
tables have no `rerun` for an option, it is read as exact and the route
reports `rerun_evidence="tested"`.

### Observations in postconditions, and routes to engines (#444)

- `sv.equivalent(rows=…, floats=sv.within(abs=…, rel=…, ulps=…), zeros=…, timestamps=…, strings=…, decimals=…, errors=…)`
  in `ensures` names what the result's consumer observes: rows as a multiset
  (the default) or a sequence, doubles exact or within a tolerance, one zero
  and one NaN, timestamps to a precision, strings up to NFC. Observations are
  ordered by refinement, component by component (`Observation.refines`), and
  `Observation.equal` compares two results up to one. Each other postcondition
  that depends on what the observation ignores says so
  (`CheckedCondition.ignores`), and the report is then not proved.
  Without `equivalent`, nothing changes.
- `Report.run(con, engine, route="auto")` chooses how the proof reaches the
  engine: natively where the plan was verified under the engine's profile,
  through the reference's translation, by the option-wise transfer check,
  or by a re-check under the engine's profile, and refuses the plan with the
  reason otherwise (`sverify.routes`, decision D13 of
  [core-semantics.md](docs/core-semantics.md)). The route goes into
  `Report.routes`; `route="native"` and the others take that route or refuse.
  `deterministic=True` refuses a plan whose result is not determined up to
  row order (D10). Each route carries the plan's class on the engine
  (`Route.cls`: refines, refines up to an observation, approx, shim or
  refused), and an engine that agrees with the reference only up to an
  observation the postcondition does not state is refused, or shimmed. A
  function the engine does not run refuses the plan with the reason. Before
  it runs, a routed run checks the preconditions, the inferred bounds and
  the assumed `SUM`s on the data (`Report.check_inputs`) and refuses a
  batch that breaks one, naming it (`PreconditionError`). Without `route`,
  `run` behaves as before.
- `semantics="polars"` checks an Ibis transformation under Polars's
  profile, once the checker has one.
- `sv.equivalent(elements="multiset")` ignores the order of a list's
  elements. A postcondition the checker does not prove, and that reads the
  value of `first` or `last` without an order or a list's element order,
  says it depends on that open choice.
- Engine profiles record the versions their facts were probed at (DuckDB
  2.0.0, Polars 2.1.0). A routed run on another version warns
  (`EngineVersionWarning`), and one on another major version is refused
  (`EngineVersionError`) until the probes are re-run (D14).

### Unspecified and clustered sort directions

A `SortRel` key may now leave its direction unspecified, read as ascending
with NULLs last, or be `SORT_DIRECTION_CLUSTERED`, any order with equal keys
adjacent; both were refused before. A window's or a measure's order still
states its direction. Lean's `Rel.AllowedP` states what each profile allows,
with `Rel.allowed_core` proving the reference within the core
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444),
`docs/core-semantics.md`, D6 and D8).

### Checking under Substrait's own semantics

`verify(semantics="substrait")` checks an Ibis transformation under
`Profile.substrait`, Substrait's semantics as its extension YAMLs state it
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)):
each option at the plan's preference among the YAML's values, any of them
where the plan states none, two zeros and signed NaNs as IEEE 754 has them,
and open wherever the YAMLs say nothing. Lean proves it refines the core
(`Profile.substrait_le_core`). The reference's proof holds there when, at
every option the plan meets, Substrait allows nothing the reference does
not; otherwise `Report.transfer` names the options. `substrait-check
--profile-diff` lists where the two profiles differ, published in
[docs/core-semantics.md](docs/core-semantics.md#the-substrait-profile).

### Substrait's own test cases run against `Profile.substrait`

The function test cases of `substrait-io/substrait` v0.106.0 run against
Substrait's profile on every pull request ([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444), step 4):
`python -m sverify_dev.substrait_cases`, with the ledger
`upstream/substrait-cases.json`. Of 1,317 cases, 631 agree, 625 are refused
and 61 disagree, each disagreement a wrong test case
([ST-13](https://github.com/AlexanderNenninger/substrait-lean/blob/main/upstream/bugs/ST-13.json), [ST-14](https://github.com/AlexanderNenninger/substrait-lean/blob/main/upstream/bugs/ST-14.json),
[ST-15](https://github.com/AlexanderNenninger/substrait-lean/blob/main/upstream/bugs/ST-15.json)).

The replay fixed four parser bugs. `negate` of an integer constant at the
least value of its type (`negate(-128::i8)`) now overflows by its `overflow`
option, where it folded to 128. A call with a list literal argument
(`cardinality([1, 2, 3])`) is read, where constant folding refused it.
`variance` and `std_dev` read their `distribution` as the leading enum
argument of their current signatures. A date minus an interval whose result
is typed as a timestamp of any precision is refused, as the date plus one is,
where it returned a date.

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

### A local `DeltaSink`'s commits log what they changed

A `DeltaSink` on a local path commits the files DuckDB wrote, and the Delta
history showed that commit as a `WRITE` with no `operationMetrics`, while
the same refresh on S3, a delta-rs MERGE, logged the rows it inserted and
deleted ([#453](https://github.com/AlexanderNenninger/substrait-lean/issues/453)).
The local commit now logs a write's metrics (`num_added_rows`,
`num_added_files`, `num_removed_files`, …) and, for a change, the ones
delta-rs's MERGE logs (`num_target_rows_inserted`,
`num_target_rows_deleted`, `num_target_rows_copied`,
`num_target_files_added`, …), with `operationParameters.sverify` set to
`merge` or `created`. The operation stays `WRITE`: delta-rs 1.6.6 refuses
another name.

### Touched frames are proved

Lean now proves the touched-frames strategy, which maintains window
aggregates over bounded RANGE frames of one time column by recomputing only
the rows near a batch's changes
([#458](https://github.com/AlexanderNenninger/substrait-lean/issues/458),
part of [#294](https://github.com/AlexanderNenninger/substrait-lean/issues/294)).
A window row depends only on the rows of its partition whose time lies in
its frame (`TouchedFrames.outRow_local`), so the rows outside
`[t0 - end, t1 - start]` keep their values and the rows inside come out the
same from the narrowed input (`TouchedFrames.framed_batch`). `status()` and
the refresh summary no longer say "tested, not proved", and
`NodeStatus.tested` is now `NodeStatus.framed`.

A window whose frames all end before the row (or start after it) lost the
output rows near the end of a batch's span: the recompute read too few
input rows. The span now always holds the row itself.

### A verify report runs the plan it checked

`Report.run(con, engine=None)` runs the plan a `sv.verify` report is about,
for an Ibis expression or a SQL query, with its `params` and `semantics`.
Running that plan used to take `sverify.contracts.plan_json`, outside the
public API. `Report.plan` holds the plan as Substrait JSON
([#461](https://github.com/AlexanderNenninger/substrait-lean/issues/461)).

### An Iceberg sink maintains its table

A streaming `IcebergSink` used to add a snapshot, a data file and a position
delete file on every refresh, so a two-row aggregate refreshed every minute
grew by some 1,440 snapshots and 2,900 files a day. `IcebergSink` now takes
`DeltaSink`'s maintenance options: `compact_every=N` compacts the table after
every N writes, rewriting the data files with position deletes and the small
files of each partition as data files of their live rows in one `replace`
snapshot, and dropping the delete files no data file reads.
`snapshot_retention=` then expires older snapshots (keeping `min_snapshots`
and the sink's own last one) and deletes the files only they referenced.
`maintain()` runs it on demand. The compaction snapshot carries the contract,
so a restarted job resumes past it, and downstream nodes read through it. With
`compact_every=4`, an aggregate refreshed 37 times holds at most 5 snapshots,
4 data files, 3 delete files and 41 files on disk, and equals a full
recompute throughout (`test_maintenance_keeps_a_streaming_sink_bounded`)
([#465](https://github.com/AlexanderNenninger/substrait-lean/issues/465)).

### A partitioned Iceberg sink takes only the change

An `IcebergSink` whose table is partitioned (identity, `day()` or any other
transform) writes each refresh as one snapshot of position deletes and new
rows in the partitions the change touches, as an unpartitioned table
already did ([#43](https://github.com/AlexanderNenninger/substrait-lean/issues/43)).
It used to overwrite the whole table in two snapshots on every refresh. The
deletes read only the data files of the partitions the deleted rows fall
in, each delete file is in the partition of its data file, and the other
partitions keep their files. Rows are split by partition without
`pyiceberg-core`, which pyiceberg 0.12 needs for every transform but
`identity`, so a `day()`-partitioned sink also works without it
([#466](https://github.com/AlexanderNenninger/substrait-lean/issues/466)).

### An Iceberg sink creates its table where and how you say

`IcebergSink` takes `location=`, `partition_by=` and `properties=`, and its
first write creates the table with them in one commit. A catalog without a
default location, such as Unity Catalog's Iceberg REST catalog on a schema
without a managed storage root, can now hold a sink, and a sink can create a
partitioned table itself (`partition_by=[("ts", "day"), ("host",
"identity")]`), which then takes each change in the partitions it touches
([#466](https://github.com/AlexanderNenninger/substrait-lean/issues/466)).
They apply only to a table the sink creates: a sink on an existing table
that differs from them warns once and leaves the table as it is
([#468](https://github.com/AlexanderNenninger/substrait-lean/issues/468)).

### Upstream bugs as JSON documents

The upstream bugs ledger is now one JSON document per bug,
`upstream/bugs/<id>.json`, in the format of `upstream/bug.schema.json`, and
the lift's backlog of tests is `python/tests/lift_backlog.json`, with a
reason for each test. `python -m sverify_dev.bugs` and `tests/test_bugs.py`
check both: the schema, unique ids that name their files, and that the files,
engine facts and tests they link to exist (#477).

### Checks on data no longer warn through pandas

The checks on data (`on_unproved="runtime"`, `requires` on bound tables, node
refreshes) counted violations with Ibis's `execute()`, which converts the count
through pandas. Under Ibis 12 and pandas 3.1 that printed a `Pandas4Warning`
about `future.infer_string`, in notebooks 4 and 5 of the tour among other
places. The counts are now fetched through Arrow
([#479](https://github.com/AlexanderNenninger/substrait-lean/issues/479)).

### A report's assumed SUM names its column

`Report.assumed` named an integer `SUM` it assumes fits 64 bits by Lean's
column index (`SUM of $2`), while the hint on the same report named the
column. The assumed line now names the column the `SUM` adds up, as the hint
does (`SUM of amount_cents`), and `Issue.column` holds it
([#480](https://github.com/AlexanderNenninger/substrait-lean/issues/480)). A
report on SQL text, and a `SUM` of an expression, keep Lean's notation.

### The installed wheel's tests skip the refusal-message scan

`test_refusal_messages.py` reads the repository's sources, which the Wheels
workflow's copy of the tests against the installed wheel doesn't have. It now
skips there, as `test_scripts.py` does, so the wheel builds pass again
([#483](https://github.com/AlexanderNenninger/substrait-lean/pull/483)).

### A sink recovers from a write that failed after its commit

A `DeltaSink` write that raised after its commit had landed, for example
reading the table's version back while the object store restarted, left
every later refresh of the node failing in the same process until a restart
([#488](https://github.com/AlexanderNenninger/substrait-lean/issues/488)).
The next refresh now finds the epoch the table committed in its transaction
version and writes on from that state, as a restarted job does. A write that
failed before its commit is replayed. This holds for every sink with a
`committed()` that reads the sink back.

### Rolling means, MIN over a sliding frame, window aggregates of expressions

Sverify verifies `AVG`, a `SUM` of doubles and `MIN` over a frame that does not
start at UNBOUNDED PRECEDING: rolling means over rows or over an interval, and
`MIN` over a sliding frame. DuckDB and Polars run them; DataFusion, which
slides a frame by retracting rows, still refuses them. A window aggregate's
argument may be an expression (`(t.qty * 2).sum().over(group_by="name")`): the
checker computes it in a projection under the window, so its overflow and
other issues are checked as a projection's
([#506](https://github.com/AlexanderNenninger/substrait-lean/issues/506)).

### A time of day plus an interval, and truncated

`t.ts.time() + ibis.interval(hours=1)` and `t.ts.time().truncate("h")` now
verify, and run on DuckDB. A time of day plus a constant interval wraps around
midnight both ways, as DuckDB computes it (`TIME '23:30' + INTERVAL 1 HOUR` is
`00:30`); an interval with months is refused. Truncation to an hour, minute,
second or millisecond is a floor of the microseconds. The SQL lift reads
DuckDB's `TIME ± INTERVAL` too. Other engines refuse both until #271
([#507](https://github.com/AlexanderNenninger/substrait-lean/issues/507)).

### typeof of a column is a constant

`t.qty.typeof()` now verifies: the Ibis producer folds `typeof` of a column to
DuckDB's name of its type (`BIGINT`, `DECIMAL(10,2)`, `VARCHAR[]`), a string
constant in the plan, so every engine gives the same name. `typeof` of an expression, a struct or a map is refused,
since the engine infers that type its own way
([#508](https://github.com/AlexanderNenninger/substrait-lean/issues/508)).

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

### A refresh that fails while committing changes nothing

A refresh that failed after DuckDB had updated a view's state in place (an
out-of-memory error, say) left the view ahead of its recorded source
versions, and the retry in the same process applied the batch a second
time: duplicated rows, then `changes delete rows that are not in the
inputs` or delta-rs's `rows failed validation check` in a sink. The commit
now updates the Python side first and DuckDB's state last, in one
transaction, and restores the old tables, versions and states on any
failure, so the retry applies the batch once
([#515](https://github.com/AlexanderNenninger/substrait-lean/issues/515)).

### A Delta source dropped and created again rewrites its sinks

A Delta source dropped and created again at the same path starts its
versions over. Its sinks had committed a higher epoch, so each refresh
skipped the write as "already committed" and kept the old table's rows,
with no error, in the same process and after a restart
([#516](https://github.com/AlexanderNenninger/substrait-lean/issues/516)).

The contract now records each Delta source's table id (`metaData.id`,
`Contract.table_ids`). When a source's id changed, or its version went
down, the sink's rows come from another table: the refresh recomputes the
node and overwrites the sink, so it holds a full recompute of the new
table. `DeltaSource.changes` reads the new table's snapshot when the table
was created again since the version asked for (the report says
"created again"), and a restarted job doesn't resume from a state stored
from the old table.

### Two processes refreshing the same `DeltaSink` no longer write a change twice

`DeltaSink` read the epoch the table had committed, then loaded the table
again and committed, so a commit by another process in between went
unnoticed. Two pods of one job during a rolling deploy, or a cron run
overlapping a slow one, could both write the same change, or write an older
change on top of a newer state, and later refreshes kept the duplicate rows
([#517](https://github.com/AlexanderNenninger/substrait-lean/issues/517)).

The commit is now conditional. It is made on a snapshot whose transaction
version (`app_id`) is still the one the refresh read, and every commit that
changes rows carries the transaction, so delta-rs's conflict check rejects a
concurrent one. The process that loses raises
`sverify.errors.ConcurrentWriteError`, naming the sink, and its write is not
committed. Its next refresh skips the state the other process committed, or
writes the whole table. This holds for local (native) commits and for
MERGE. A sink of your own raises the same error to get the same recovery.

### Exact median, quantiles, mode and arg_min/arg_max

Sverify now verifies the exact quantiles, the mode and `arg_min`/`arg_max`
([#53](https://github.com/AlexanderNenninger/substrait-lean/issues/53)), from
Ibis (`median()`, `quantile(q)`, `mode()`, `argmin()`, `argmax()`) and from
DuckDB's SQL (`median`, `quantile_cont`, `quantile_disc`, `quantile`,
`mode(x ORDER BY …)`, `arg_min`, `arg_max`), and runs them on DuckDB:

- `quantile_disc(x, q)` is the value at position `⌈n·q⌉` of the values in
  order; `quantile_cont(x, q)` and `median(x)` interpolate between the two
  neighbours at `(n−1)·q`, of doubles or of integers converted. `q` is an
  exact decimal in `[0, 1]`. Contracts know a median or quantile lies within
  its column's range.
- `mode` breaks ties by its own `ORDER BY`, and is refused without one;
  Ibis's `mode()` takes the smallest of the most frequent values.
- `arg_min(x, y)` is `x` at the row with the smallest `y`, over the rows where
  neither is NULL; ties are the engine's choice unless a key settles them, as
  for `first()`.

What DuckDB 2.0.0 does with each is recorded as engine facts
(`duckdb-quantile-disc`, `duckdb-quantile-cont-interpolation`,
`duckdb-mode-ties`, `duckdb-arg-min-nulls`). Other engines refuse them until
[#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271), and
approximate quantiles stay refused
([#469](https://github.com/AlexanderNenninger/substrait-lean/issues/469)).
H2O's groupby q6 and the catalogue's median and arg_max queries now verify.

### A recreated Iceberg source no longer leaves its sinks stale

An Iceberg table dropped and created again under the same identifier is
another table, even where its sequence numbers reach the old ones. An
`IcebergSource` now records the table's UUID with each version it reads,
and sinks record it in their contract (`Contract.table_ids`), as Delta
sources do with their table id since
[#516](https://github.com/AlexanderNenninger/substrait-lean/issues/516). A
refresh then reads the new table in full, and a restarted job recomputes
its nodes instead of resuming from rows of the old table
([#533](https://github.com/AlexanderNenninger/substrait-lean/issues/533)).

### Two writers of one `IcebergSink` no longer apply a change twice

An `IcebergSink` now commits only while the table still holds the epoch it
read, as a `DeltaSink` does since
[#517](https://github.com/AlexanderNenninger/substrait-lean/issues/517). When
two processes refresh the same sink, the one that commits second raises
`ConcurrentWriteError`, also where pyiceberg would retry its commit on top
of the other writer's snapshot, and where both create the table. Its next
refresh writes the whole table, or skips the state the other writer
committed
([#534](https://github.com/AlexanderNenninger/substrait-lean/issues/534)).

### Window variance, unordered STRING_AGG, signed Ibis frame offsets, divisor suggestions

`VARIANCE` and `STDDEV` (of a sample or a population) now verify over a
window ([#54](https://github.com/AlexanderNenninger/substrait-lean/issues/54)).
Over a frame they are the reference's own two passes, which DuckDB runs
exactly; other engines refuse them for now (#271).

`group_concat()` / `STRING_AGG` without an order verifies: the strings may come
in any order, so `verify` reports the plan as not deterministic and proves no
postcondition about it. DuckDB joins them in the input's order.

Ibis windows with a negative offset count the other way, as Ibis means them:
`following=-1` is `1 PRECEDING`. Ibis's own SQL writes `-1 FOLLOWING`, which
DuckDB refuses ([IB-4](upstream/bugs/IB-4.json)).

`verify` now proposes a precondition for a division by an aggregate: each value
at least 1 (or 0.01 for a decimal) for a `SUM`, and the column NOT NULL for a
grouped `COUNT` (`_.size >= 1`, `_.user_id.notnull()`).

### Polars refuses `regexp_match` patterns with flags or lookarounds

The Polars engine counted the entries of `regexp_match` by asking Polars, so it
ran patterns with `(?i)`, named groups or lookarounds, where the reference
model raises a bad-regex error (`Text.simpleRegex`). It now counts groups as the SQL writer
does and refuses those patterns too, in one definition shared by both
([#544](https://github.com/AlexanderNenninger/substrait-lean/issues/544)).

### `QUANTILE_CONT` between `-inf` and `+inf` raises (#561)

`QUANTILE_CONT` and `MEDIAN` whose neighbouring values are `-inf` and `+inf`
now raise a domain error in the reference, as a NaN created from numbers does
(`AggFn.makesNan`). IEEE's interpolation, and DuckDB's, is NaN there; the
reference used to clamp it to `+inf`, so engines disagreed. A plan that may
meet it is reported as a possible domain error, ruled out by a precondition
that bounds the column, and the SQL sverify writes for DuckDB raises where
the interpolation is NaN and no value is. Per D17, this changes the reference
and ships in a minor version bump.

### More of `ε`: scalar rules, thresholds and relative bounds

`epsilon_by_engine` now carries `ε` through `abs`, `FLOOR`, `CEIL`, `ROUND`,
casts to integers and `sqrt`, each by a rule proved in
`float-bounds/FloatBounds/Propagate.lean`
([#568](https://github.com/AlexanderNenninger/substrait-lean/issues/568)). A
comparison is exact where its sides' ranges, widened by `ε`, do not meet, so a
filter or key on it keeps the same rows; the contract reports per engine
whether every filter, key and sort does (`"rows_exact"`). A column whose
range leaves out zero gets a relative bound too, and a difference of nearly
equal values gets none
([docs/float-bounds.md](docs/float-bounds.md#through-arithmetic)).

### Doubles: no operation creates `±∞` (#575)

The reference now raises where an operation on finite doubles overflows to
`±∞`: `+`, `-`, `*`, `/` and `power` (`1e308 * 10`, `power(0, -1)`), `exp`
past `709.78`, and a `SUM`, `AVG`, variance or covariance of finite values.
`verify` rules the error out by an inferred precondition, as for a `SUM` that
leaves 64 bits: a `SUM` or `AVG` of bounded values over a bounded number of
rows (`max_rows`) is proved finite (#85's error bounds), and elsewhere
`Report.assumed` lists the precondition ("stays finite where its inputs
are") and the job checks it on the data: the SQL sverify writes for DuckDB
raises `overflow to infinity` where it fails, and so does the Polars engine.
With `infer=False` it is an error that makes the report unproved. A plan verified
with `semantics="duckdb"`, where DuckDB's `±inf` is the answer, makes no such
assumption, and `Report.run` writes no check of it. `±∞` from
the data passes through as before. So a plan verified under the reference
creates no NaN and no `±∞` its inputs did not hold
([#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575),
fact `duckdb-double-overflow`, spec gap `ST-9`).

### `Report.run` refuses an overflow to `±∞` before the run (#575)

`report.run(con, engine)` now checks the assumption that no operation on
finite doubles gives `±∞` on the data before the run, as it already did for
an assumed `SUM`: it runs the proved DuckDB translation first and refuses the
batch with a `PreconditionError` that names the operation, so nothing runs on
the engine. A refresh of several nodes stays atomic per node: the node whose
batch overflows writes nothing, while the stored nodes upstream of it, whose
results it reads, keep the epoch they committed.

### Bounds of one double operation, and `exp`

A double `+`, `-`, `*`, `/` or `exp` whose inputs' bounds keep the result
below the largest double no longer needs a "stays finite" check on the data,
and chains of them have bounds
([#582](https://github.com/AlexanderNenninger/substrait-lean/issues/582)).
`exp` propagates `ε` too, trusted to one ulp of the platform's `libm`
([docs/float-bounds.md](docs/float-bounds.md#one-operations-bounds-and-overflow-582)).

### Preconditions that relate columns are used in proofs (#597)

A precondition of any shape, such as the implication
`(_.a <= 0) | (_.b < 0)`, is now kept whole as a fact about each row. A
postcondition that restates it is proved wherever the plan carries it
through: projections that keep its columns, filters, sorts, limits, joins
and `UNION ALL`s whose inputs all have it. Under a filter or in a `CASE`
branch, the disjuncts that cannot be TRUE drop out and the rest narrows the
columns: under `t.filter(_.a > 0)` the implication gives `b <= -1`, also
when `a` or `b` may be NULL. Before, these postconditions were reported as
"TRUE or FALSE". Filter conditions are kept whole the same way. Steps 1 and
2 of #597; see `docs/tasks.md`.

### `AND` and `OR` evaluate both operands, and the report says so (#604)

An error in either operand of `AND` or `OR` may raise, whatever the other
operand's value, as DuckDB and Polars evaluate both (decision D19 in
`docs/core-semantics.md`). The checker already analysed both operands. A
plan such as `filter((x != 0) & (10 // x > 1))` was proved only under the
precondition `x != 0` that `verify` inferred, and `Report.run` did not check
it, so a batch with `x = 0` raised on the engine (now refused: see the next
entry). The report now flags an error inside an `AND` or `OR`
(`Issue.under_and_or`) and suggests guarding the operation itself:
`(CASE WHEN x <> 0 THEN 10 // x END) > 1`, in Ibis
`ibis.cases((_.x != 0, 10 // _.x)) > 1`, which is proved without the
precondition.

### `Report.run` checks the preconditions first (#604)

`report.run(con, engine)` checks the report's preconditions on the tables
before the run, with or without `route=`: `requires` and the bounds `verify`
inferred. A batch that breaks one is refused with a `PreconditionError`
that names it, and nothing runs, as the reference's first guarantee promises.
Before, a plan proved under an inferred precondition (such as `x != 0` for
`filter((x != 0) & (10 // x > 1))`) ran on the batch and raised on the engine.
`check_inputs=False` skips the check for a caller that has made it already,
and gives up the guarantee on data that breaks a precondition.
`Node.refresh` already checked them on each batch.

### Constants that raise raise for the whole plan (#609)

A constant subexpression that raises, such as `1 // 0 = 1` in a later
`CASE WHEN`, now makes `verify` report the plan as raising, whatever the data
and whichever branch the rows take. DuckDB evaluates a `CASE`'s constant
conditions when it plans the query, so such a plan raised on any data, an
empty table included, though `verify` had proved it. The issue is flagged
`constant`, and the report says no precondition rules it out (D21). This
changes the reference and ships in a minor version bump (D17).

### `ABS` of a narrow integer

`verify` no longer crashes on `abs` of an `int8`, `int16` or `int32` column ([#616](https://github.com/AlexanderNenninger/substrait-lean/issues/616)). The model checks `ABS` at the column's width, as DuckDB does: `abs(-128::TINYINT)` raises, where the model gave 128 and the written plan returned it as a BIGINT, and the inferred bound stays within the column's type: `v >= -127` for an `int8`. An inferred bound never reaches `2**63`, and a SQL comparison of a narrow column with a constant that fits it compares the column itself, so such a bound in `requires` is used by the proof.

### The smallest BIGINT in messages

Reports and counterexamples print the smallest `BIGINT`, `-9223372036854775808`, as an integer; they showed it as the double `-0.000000d` ([#619](https://github.com/AlexanderNenninger/substrait-lean/issues/619)).

### Rankings with their own ORDER BY are refused

The SQL lift refuses `rank`, `dense_rank`, `row_number`, `percent_rank` and `cume_dist` with an `ORDER BY` of their own (`cume_dist(ORDER BY id) OVER (… frame)`), which DuckDB ranks within the frame. They were lifted as a plain rank over the partition, a wrong result in Lean and in the written SQL ([#625](https://github.com/AlexanderNenninger/substrait-lean/issues/625)).

### Three SQL lift refusals

The SQL lift refuses `x IN map(…)`, which it read as `FALSE`; an `INTERVAL '… ago'`, whose `ago` SQLGlot drops from a single unit (upstream/bugs/SG-8.json); and a cast to `TIMESTAMP(p)` for p from 0 to 3 or 7 to 9, which DuckDB keeps at seconds, milliseconds or nanoseconds where the lift kept microseconds. Each gave a wrong result in Lean and in the written SQL ([#626](https://github.com/AlexanderNenninger/substrait-lean/issues/626)).

### Times in nanoseconds are refused

A table with a column of times in nanoseconds (`time64[ns]`, DuckDB's `TIME_NS`) is refused when it is added: Ibis's time type has no unit, so the plan read the column as microseconds while the engine kept the nanoseconds, and a `::TIME` cast was lost ([#627](https://github.com/AlexanderNenninger/substrait-lean/issues/627)). Cast such columns to `time64[us]` first.

### Decimals in lists and structs print with their scale

Rows and counterexamples print a decimal inside a list or struct with its scale: `[1.0, 2.5]` for a `DECIMAL(4, 1)[]`, which printed as `[10, 25]` ([#628](https://github.com/AlexanderNenninger/substrait-lean/issues/628)). The values `Rel.eval` and the written plans compute were right.

### Reports and refusals in the user's terms (#655)

- Issues name columns and the Ibis or SQL operator (`total // qty`,
  `sum(x)`, `x / 0`) where Lean's notation said `($3 / $2)` or `$1`, and a
  domain error of a double `SUM` names its cause (NaN from +inf and -inf).
- An inferred precondition says where it came from: `requires t: (_.qty !=
  0) (inferred from total // qty)`, and a batch that breaks it is refused
  with the fix (filter those rows first, a CASE, or state it).
- The AND/OR hint writes out the guard for the user's division; the
  "it comes from it divides by 0" hint names the constant divisor.
- No more "assumes … stays finite" next to "may fail: division by zero"
  for the same operation; the NULL hint names the nullable columns and is
  dropped where none is; an unproved key says to add `sv.unique(...)`.
- An engine setting refuses only where the plan relies on it (a sort's
  NULLS LAST is spelled out, so `default_null_order` warns), and the
  refusal gives the `SET GLOBAL …` that restores it.
- A refused transfer leads with "verify with semantics='reference' to run
  on polars".
- Function refusals use the Ibis or SQL name (`median() or quantile()`,
  `re_extract()`), say which engine runs it and link #271 in full;
  `now()`, `current_timestamp` and `random()` in SQL are refused as
  non-deterministic; the SQL lift quotes the SQL, not SQLGlot's node.
- Refusals name a stored node by its transform (`mean (stored as m)`), and
  the fix for a non-deterministic result is kept on every route.

### Inferred preconditions are errors by default: `on_inferred=` (#655)

A precondition sverify infers to rule out a runtime error (`amount * 2` needs
`_.amount < 2**62`, `total // qty` needs `_.qty != 0`) is no longer assumed
silently, since checking it on the data refuses batches the user never asked
to refuse. `sv.verify` and `sv.transform` take `on_inferred=`:

- `"error"` (the default): the plan is not proved without it. The report
  lists each one under `needs:` (`Report.needed`) with where it came from and
  the fixes: declare it in `requires` (each run then checks it on the data),
  or rewrite so no row needs it (filter those rows first, or a CASE). A
  transform raises `VerificationError`, and `Report.run` and `refresh` refuse
  the plan with the same text.
- `"warn"`: assumed and checked on the data as before, with an
  `InferredPreconditionWarning` naming each one.
- `"silent"`: assumed and checked as before.

`infer=False` still turns inference off: an overflow is then an error whose
hint names the bound. Declared `requires` are checked on the data as before.
`SUM`s assumed to fit and double operations assumed to stay finite
(`Report.assumed`) are not inferred preconditions and keep their run-time
checks.

### Route classes: exact, observed, shim, refused (#655)

A route's class (`Route.cls`) is one of four: `exact` (every result the
engine gives is one the reference allows; was `refines`), `observed` (equal
to one up to an observation; was `refines_up_to` and `approx`, since a
tolerance is an observation of doubles), `shim` and `refused`. An observed
route keeps the observation in `Route.observation` (its components, and the
tolerance the plan's bound gives) and whether that bound is proved in
`Route.bound_proved`. Messages and docs say "observation" where they said
`q`; sverify reads a choices row's `"observation"` and `"rerun_observation"`
keys, and still the checker's `"q"` and `"rerun"`. `docs/realizability.md`
labels its cases the same way.

### Doubles into a sink work without extra settings (#655)

A sink's `reproducible` now defaults to rows as a multiset, doubles within
the bound the checker proves for the plan (`Report.epsilon`), and other
values exact: `sv.equivalent(floats="plan")`, the new `floats="plan"`
level. A run whose `ensures` names no observation checks the engine against
the same default, except in the double columns a proved postcondition
reads, which keep their exact value. So a mean into a `DeltaSink` refreshes
on DuckDB and Polars with no `reproducible=` and no `ensures`. A sink whose
consumers need the same bits on a rerun states `reproducible=sv.equivalent()`.
A refusal over a tolerance names the smallest one that passes.

### Suggestions that make a plan verify (#655)

- A postcondition that fails only where a column is NULL (`TRUE or NULL`)
  gets an `IS NOT NULL` precondition on the input column it reads
  (`length(s) >= 0` needs `_.s.notnull()`), inferred and reported under
  `on_inferred` like a bound: listed under `needs:` by default, assumed with
  `"warn"` or `"silent"`. A postcondition that may also be FALSE no longer
  gets the NOT NULL advice.
- A result not determined up to row order names the `sv.unique(...)` that
  determines it, the partition (or grouping) and order columns of its
  windows and ordered aggregates (`Report.ties`); a route refused for a rerun
  carries it in `Route.suggested` and its message.
- A route refused because the plan's bound on doubles exceeds a stated
  tolerance (in `ensures` or `reproducible=`) names the `sv.max_rows(N)`
  under which it fits, the bound growing linearly with the rows, or says
  that no row cap does (`Route.suggested`).

### Unproved plans no longer run silently (#655)

`Report.run`, `Node.refresh` and a group's `refresh` refuse a plan whose
report is not proved, with what was not proved in the user's terms:
`refused on duckdb: not verified: may fail: domain error: sum(x) (see
report.errors)` (`sverify.errors.RouteError`). `unverified=True` runs it
anyway and says so: an `UnverifiedRunWarning`, the route `"unverified"` in
`Report.routes` or `StageRefresh.route`, and `sverify.verified: false` in
the result's schema metadata. `route="auto"` is the default: every run
chooses how its proof reaches the engine (`sverify.routes.choose`), and
`route=None` is gone.

### A verified plan for any Substrait consumer

`report.to_substrait(format="json" | "binary")` returns the verified plan for
any conforming consumer of Substrait 0.106, with each option the proof
depends on pinned in the plan, and its contract (`requires`, declared,
inferred and assumed, and `ensures`, with a manifest) as metadata in the
plan's `advanced_extensions`. `shims="apply" | "annotate" | "refuse"`
decides what happens at a spec gap: rewrite it into well-specified
Substrait, ship it as an assumption, or refuse. `sv.from_substrait` reads an
export back and proves its contract again; `report.substrait_contract()`
gives the contract as JSON for a sidecar, and `sverify.errors.ExportError`
names the gap a refusal meets
([#664](https://github.com/AlexanderNenninger/substrait-lean/issues/664),
[docs/how-to-export.md](docs/how-to-export.md#exporting-to-substrait)).

### Proved file pruning: Iceberg, string bounds, NaN and implied predicates

`IcebergSource` takes `where=` as `DeltaSource` does: the source is the rows
on which the condition is TRUE, and snapshots, native scans and appends read
only the data files whose statistics do not rule it out. Both sources now
also skip files by string bounds, which Delta and Iceberg may cut to
prefixes, for `=`, `<`, `<=`, `>`, `>=` and `IN` of a string column and a
literal. `SubstraitLean/Pruning.lean` proves the criterion against the exact
statistics semantics, with NULL counts, NaN left out of double bounds and
truncated string bounds, and that every plan linear in the source gives the
same result from the files kept (`Rel.eval_pruned`). For `amount * 2 > 100`,
pyarrow's statistics pushdown reads every file and sverify skips those with
`amount <= 50` (`test_iceberg_where_skips_files_the_reader_would_scan`).

A node now also prunes from predicates its view implies on a source and the
query does not state. With `o.ts >= c.since` in a join of orders and
customers, and `since >= DATE '2026-01-01'` among the customers'
preconditions, the orders source reads only orders from 2026 on and skips
older files. Lean derives the predicate from the preconditions, Delta CHECK
constraints and source conditions, and proves that the view's result is the
same (`Rel.need_eval` in `SubstraitLean/Implied.lean`). `Report.implied`
lists the predicates a transformation implies on its inputs
([#81](https://github.com/AlexanderNenninger/substrait-lean/issues/81)).

### Per-expression guard elimination

Guard elimination dropped the run-time checks of a whole plan or none of
them (`Report.guard_free`). A report now lists the expressions that cannot
raise on data that meets the preconditions, `Report.unchecked`, and
`to_sql(plan, dialect, unchecked=report.unchecked)` leaves out only their
checks: in `SELECT a // b, a * b` with `b >= 1`, the division loses its
`CASE` and the product keeps its overflow check. `Rel.evalG_marks` in
`SubstraitLean/Guards.lean` proves the result unchanged
([#83](https://github.com/AlexanderNenninger/substrait-lean/issues/83)).

### The chaos suite fails again on the signatures of #515, #516 and #517

Their fixes are on main, so `python/tests/chaos/known.json` no longer lists them, and a scenario that hits one again fails the run.

### A crash-injection suite for pipeline execution

`python/tests/chaos/` fails refreshes on purpose: an exception or a SIGKILL at
each step of a refresh (reading a source, the engine, the pipeline's state,
the cursors, a Delta or Iceberg sink before, during and after its commit),
an object store that goes away and comes back, sources that change or
vanish mid-refresh, and two processes racing on one sink. After each, the
same process or a fresh one refreshes, and every sink must equal a full
recompute of its inputs, with its epoch the sum of the versions it records.
Each failed scenario streams a record to a JSONL ledger, and
`python -m sverify_dev.chaos summarize` groups the failures by signature.
`poe test-chaos` runs it; `qa` and CI leave it out. It found
[#515](https://github.com/AlexanderNenninger/substrait-lean/issues/515),
[#516](https://github.com/AlexanderNenninger/substrait-lean/issues/516) and
[#517](https://github.com/AlexanderNenninger/substrait-lean/issues/517).

### Examples and searchable ledgers on the docs site

The docs site has two new sections. Examples
([docs/examples.md](docs/examples.md)) shows sverify's features in eight short
steps: a contract proved and run, SQL through `sv.verify`, inferred
preconditions refusing a bad batch before the run, routes to Polars and their
classes, doubles within a tolerance, a reproducible sink kept up to date,
a plan checked under DuckDB's profile, and Substrait's own semantics. Ledgers
renders the upstream ledger (bugs and Substrait spec gaps), DuckDB's and
Polars's characterization facts, the checklist's coverage per engine and the
realizability table from their JSON at build time, one anchor per entry, so
the site's search finds an entry by id, engine, function, option or text, and
the ledgers' index filters them. The README and the tour's notebooks describe
routes, observations, reproducible sinks, the inputs checked before a run and
the stricter reference.

### No more hangs when DuckDB frees a resident table

A refresh could hang for good in `sverify._duckdb.cursor`: opening a cursor
holds the module's lock, and when the garbage collector ran then, a
resident table's finalizer (`forget`) waited on the same lock. The lock is
now reentrant, and `collect` keeps what a finalizer queues while it runs
(`tests/test_duckdb_lock.py`).

### `homelab_qa.sh` takes its worker count, niceness and directory prefix from the environment

`PYTEST_XDIST_AUTO_NUM_WORKERS`, `HOMELAB_QA_NICE`, `HOMELAB_QA_PREFIX` and `HOMELAB_QA_CHECK_GENERATED` override the defaults (6, 10, `substrait-lean`, true). The Lean build and the tests run in separate memory scopes, the build's capped by `HOMELAB_QA_BUILD_MEMORY_MAX`, so the background chaos run can build at 8 GB and test at 2 GB beside one QA run.

### Notebook 5 no longer pins SQLGlot

`05_pipelines_and_engines.py` pinned `sqlglot==30.27.0`, which conflicts with
sverify's `sqlglot~=30.17.0` from PyPI, so the notebook couldn't be published
for 0.4.0. It now takes SQLGlot from sverify.

### `power(-inf, y)` raises for a fractional `y`

`power(-inf, y)` for a finite `y` that is not an integer is now a domain
error of the reference, as `power(-8, 0.5)` already was. IEEE 754 gives `+inf`
(`y > 0`) or `0` (`y < 0`), as DuckDB does, but Polars's `** 0.5` gives NaN;
raising lets every engine run a verified plan without a shim. A plan that may
meet it is reported as a possible domain error, ruled out by a precondition
such as `x > float("-inf")` on the base. Integer exponents keep IEEE's value
(fact `duckdb-R15-power-neginf`). Per D17, this changes the reference and
ships in a minor version bump.

### DuckDB's statistical aggregates are proved

DuckDB's `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` (Welford's update with
Chan's merge) are proved to have the properties the reference allows, so
their `stat_algo` row rests on a proof
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444),
[docs/float-bounds.md](docs/float-bounds.md)). Polars's stay tested.

### Tie order is open in the reference

The reference that plans are verified under leaves the order of ties open
(`tie_order`, `tie_pick`); the deterministic profile fixes it (D24,
[#679](https://github.com/AlexanderNenninger/substrait-lean/issues/679)).
`verify` proves postconditions and keys over every order of the ties: a
postcondition over a window, `first()`, `group_concat()` or a `LIMIT` over
ties is proved when it holds for every order, where the report used to say
`undetermined`. `Report.tie_places` names each window, ordered aggregate and
`LIMIT` whose order is not total.

### Reports as data for tools built on sverify

What sverify-dbt, a package that checks dbt projects with sverify, needed
from the public API
([#177](https://github.com/AlexanderNenninger/substrait-lean/issues/177);
the gaps left open are [#699](https://github.com/AlexanderNenninger/substrait-lean/issues/699) to [#710](https://github.com/AlexanderNenninger/substrait-lean/issues/710)):

- `sverify.errors.Unsupported` is the one class every refusal raises: the
  SQL lift's and the Ibis producer's, the SQL writer's and the Polars
  translator's derive from it. `sverify.engines.Unsupported` is the same
  class; before, `verify`'s refusals of SQL escaped
  `except sverify.engines.Unsupported`.
- `Report.needs` lists the preconditions `on_inferred="error"` needs as
  `Needed` records: table, column, comparison, bound, the condition as SQL
  and as the Python `requires` takes (`code`, `_.qty != 0`), and the
  runtime error each rules out.
- `CheckedCondition.reason` says why a postcondition is not proved, as a
  code (`"not_a_key"`, `"may_be_false"`, `"may_be_null"`, `"ties"`, …), and
  `CheckedCondition.condition` is the condition as it was given.
- `verify(tables=...)` takes DuckDB's type names (`{"id": "BIGINT", "name":
  "VARCHAR NOT NULL"}`) beside Ibis's.
- The SQL lift reads `IS [NOT] TRUE` and `IS [NOT] FALSE`.
- The checker's pipes close when it stops, so a script no longer ends with
  a `ResourceWarning`.

### Deterministic runs name the open ties

`choose(deterministic=True)`, an incremental refresh and a sink's
`reproducible=` ask for the deterministic profile (D24,
[#679](https://github.com/AlexanderNenninger/substrait-lean/issues/679)). A
plan whose ties stay open is refused there, and the reason names each window,
ordered aggregate or `LIMIT` (`Report.tie_places`). Without them the plan
runs with the engine's own order of the ties, which every proof covers. The
catalogue accepts any order the reference allows (`substrait-check
--eval-choices`, `sverify.testing.lean_choices` and `allows_rows`), so
`iot-downsample` and `pa-string-agg` match on DuckDB without `tie_order`.

### Reading a contract's proof without running it

For tools that read a proof, such as an editor, a CI step or dbt
([guide](docs/how-to-command-line.md#checking-without-running), #682):

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

### One model for doubles; every route has a class

Stating no observation, `sv.equivalent(floats="plan")` and the plan's own
bound are one observation (#689). `report.observation` prints it with the
bound, `equivalent(floats=plan, ≤ 2.2e-10)`, and `report.observation.equal`
compares doubles within it. A postcondition that reads a double keeps its
exact value under a stated `floats="plan"` as it does without one.

`verify` checks a stated tolerance (`abs`, `rel` or `ulps`) and
`floats="exact"` against the plan's bound on each engine
(`report.floats_on`). The report's `observes:` line shows the plan's bound
beside the tolerance and the engines that meet it; where none does, the plan
is not proved and the line gives the reason and a tolerance that would do.
A run used to refuse a too-tight `rel` or `ulps` only at run time.

A route prints `rows='multiset'` for a plan with no `ORDER BY`, and the
Substrait manifest's `class` is `observed` for a plan with a bound on its
doubles, as its routes are. `Observation`'s repr is its `equivalent(...)`
form.

Every verified run records one of the four classes in `Route.cls`: a plan
whose options have no row in the engine's tables, such as a `LAG` over a
unique key, is `exact` on tested evidence (#696).

### Docs: Ibis `//` floors and `%` truncates, and a hint for the pair

The guide has a section, "Integer division in Ibis and SQL", with the quotient and remainder of `-7` under each front end and semantics ([#693](https://github.com/AlexanderNenninger/substrait-lean/issues/693)). A report carries a hint when one plan uses Ibis `//` and `%` on the same operands, since `q * d + r == x` fails for negative `x`. Ten wrong statements and gaps in the README, `docs/` and the `Contract` docstring are fixed ([#698](https://github.com/AlexanderNenninger/substrait-lean/issues/698)).

### `MIN` and `MAX` of doubles run on Polars

`MIN` and `MAX` of doubles, as aggregates and as window functions, run on
Polars by `route="auto"` ([#697](https://github.com/AlexanderNenninger/substrait-lean/issues/697)).
Polars's `min` and `max` skip NaN and may keep either zero
([polars-min-max-nan](characterization/polars/facts/polars-min-max-nan.json),
[polars-min-max-zero](characterization/polars/facts/polars-min-max-zero.json)):
the translation gives `MAX` of a group with a NaN as NaN, the greatest double,
and reads both results with one zero. The shim `max_nan_greatest` and
`Polars.min_ignore_nan` are proved in `SubstraitLean/PolarsShims.lean`, and
the route's class is `shim`.

### Ranks need no key, and keys pass through joins

`RANK`, `DENSE_RANK`, `PERCENT_RANK` and `CUME_DIST` give tied rows the same
value, so a window of them is deterministic without a key on its order
(`window_tieFree`).

Columns that an inner join's condition or a filter's equality ties together
count as one column for keys (`KeyOn.eqVariants`,
[#694](https://github.com/AlexanderNenninger/substrait-lean/issues/694)).
After `p JOIN customers c ON c.customer_id = p.customer_id`, a key on
`p.customer_id` is a key on `c.customer_id` too, so a dbt model that projects
the dimension's column proves `unique(customer_id)`, and a window ordered by
`revenue DESC, c.customer_id` is determined. A left join's right copy stays
out: its unmatched rows hold NULL there.

Both come from the API critique
([#686](https://github.com/AlexanderNenninger/substrait-lean/pull/686),
[#679](https://github.com/AlexanderNenninger/substrait-lean/issues/679)).

### Reports and exceptions in your terms, hints a proof has checked

- A report names each issue by the expression you wrote: Ibis's `//` is one
  issue, `(price - cost) * 100 // price`, where it was ten about the
  reference's rewrite of it; a column computed on the way has its name
  (`ts - lag(ts)`, `sum(amount)`, `mean(temp_c) or std(temp_c)`), never a
  position like `$1`; a cast reads `CAST(amount AS DECIMAL(10, 2))`, an
  interval `ibis.interval(minutes=5)`, and conditions print `datetime(9999, 1,
  1)` where they printed `datetime.datetime(9999, 1, 1, 0, 0)`
  ([#687](https://github.com/AlexanderNenninger/substrait-lean/issues/687)).
- A report's first line is its verdict, `proved` or `NOT proved:` with what
  is missing, counted (`Report.verdict`). A `VerificationError`'s message is
  that count, then one line per finding with its hint, each hint once; the
  full report is `e.report`.
- Route lines lead with the class, in words: `shim (integer division
  rewritten to truncate); evidence proved`, `observed: doubles within
  abs=2e-07; evidence tested`. `Route.reason` keeps the long form.
- The ties note names functions in your transformation's language, and
  messages say "the checker" or "sverify" where they said "Lean".
- `sv.approx` checks its condition when you call it, an Ibis typing error in
  a condition names the condition (`ensures condition 2, …, does not
  type-check`), and a checker built before a change to the Lean sources
  raises `CheckerVersionError` with the command that rebuilds it.
- Every hint carries code a proof has checked, or there is none
  ([#688](https://github.com/AlexanderNenninger/substrait-lean/issues/688)):
  bounds that rule an overflow out are verified again before they are shown;
  a key is suggested on the input it comes from only where it proves the
  output's key, and a key lost through a join says so; a postcondition that
  fails only on a NULL output suggests allowing it
  (`(_.sd_t >= 0) | _.sd_t.isnull()`); the AND/OR hint fires only on an `&`
  or `|` you wrote; the ties note suggests a `unique(...)` only where it
  determines the result.

### Guarded double arithmetic raises nothing, and keeps its sign

Under `semantics="duckdb"`, `+`, `-`, `*` and `/` of doubles no longer
report a domain error. DuckDB gives NaN for `inf - inf`, `0 * inf` and
`inf / inf`, and the lift writes that NaN as a `CASE` around the
operation. The check now sees that the `CASE` rules the NaN out: a
condition joined with `AND` leaves its `ELSE` branch with alternatives
(`Expr.cstrAlts`), and `x ≠ 0` or `x ≠ ±inf` rule out a NaN case
([#702](https://github.com/AlexanderNenninger/substrait-lean/issues/702)).
A query's own `CASE WHEN x <> 0 AND y <> 0 THEN x * y END` benefits too.

A sum or product of non-negative doubles, and a quotient of one by a
positive one, is proved at least `0`: rounding keeps the sign. `x * y` of
`x, y ≥ 0` used to be bounded below by `-8.9e-16`, so `SUM(qty * price) >= 0`
was not proved. The three facts this rests on are proved in
`float-bounds/` ([#441](https://github.com/AlexanderNenninger/substrait-lean/issues/441)).

### The SQL lift reads md5 and sha256

DuckDB SQL with `md5(s)` or `sha256(s)` is lifted as the digests the Ibis
producer already wrote for `hexdigest`, where it used to be refused. A
dbt surrogate key from `dbt_utils.generate_surrogate_key` now verifies, and
its `not_null` test is proved
([#725](https://github.com/AlexanderNenninger/substrait-lean/issues/725)).

## 0.4.0 (2026-11-03)

### Breaking changes

Upgrading from 0.3.0, check these first. Each has its own entry below.

- `sv.sql(query)` uses the reference semantics by default, as `sv.verify` and
  `@sv.transform` do (#411). Write `sv.sql(query, semantics="duckdb")` where
  you relied on DuckDB's NaN and `±inf`.
- SQL strings are DuckDB's SQL, read by sverify's own lift. DataFusion's SQL
  planner (#211) and Isthmus (#253) are gone as frontends:
  `sverify.engines.isthmus_json`, `sverify.engines.SQL_PRODUCERS`,
  `sv.connect(sql_producer=...)`, `SVERIFY_ISTHMUS` and `sverify.engine.to_sql`
  are removed. In DuckDB's SQL `7 / 2` is 3.5; write `7 // 2` for integer
  division. `sverify.engines.to_sql` writes SQL from a checked plan.
- `@sv.transform(strict=True)` is `@sv.transform(infer=False)`, and
  `ContractedTransform.strict` is `.infer`, with the opposite truth value
  (#409). `strict=` still works and warns.
- `sv.references(col, table, other)` is
  `sv.references(col, to=other_table.other)` (#412). The positional form still
  works and warns.
- `Connection.datafusion` is deprecated and warns (#413). Run DataFusion
  through `engine="datafusion"`.
- Integer overflow at the declared width is an error that makes a report
  unproved, where it was a warning (#202). Inferred bounds (#244) discharge
  most of it; for the rest, the report's hint names the bound to add to
  `requires`. An integer `SUM` that may overflow is listed in
  `Report.assumed` and checked on the data.
- A double divided by zero raises (#204), and no operation creates a NaN
  (#257): `verify` reports both unless the plan rules them out. Bound the
  divisor or the operands in `requires`, or filter.
- Strings have fewer than 2³² characters, and `substring` with an offset or
  length outside that range is an error (#336). `verify` reports it for a
  column offset unless `requires` bounds it, for example
  `_.start >= -2**32` and `_.start < 2**32`.
- Arithmetic on `FLOAT` (fp32) is refused (#208); cast to `DOUBLE` first.
- No wheels for Intel macOS. There pip and uv build sverify from the sdist,
  which needs [elan](https://github.com/leanprover/elan).
- The maintainer tooling (`sverify.coverage`, `sverify.catalogue`,
  `sverify.fuzz`, `sverify.duckdb_fuzz`, `sverify.slt`, `sverify.examples`)
  is no longer in the wheel.

### DuckDB writes Delta and Iceberg sinks

When a node runs on DuckDB, its `DeltaSink` and `IcebergSink` have DuckDB
write the Parquet files, and sverify commits them with the contract and the
epoch, exactly once as before. The state and the rows never pass through
Python. A Delta change rewrites only the files that hold deleted rows and
adds a file of the new rows, in one commit with delta-rs's statistics; an
Iceberg change is a data file with field ids and a position delete file.
Other engines, partitioned or remote tables, and an overwrite by another
plan write through delta-rs and pyiceberg as before.

A Delta sink no longer mistakes its own constraint for a foreign one when the
node's guarantee has a decimal number: Delta stores `x >= 0.0` as `x >= 0`
(#173).

### Incremental views keep their state in DuckDB

On DuckDB, an incremental view's state no longer lives in Python: DuckDB
holds it between refreshes, and the view's rows are a DuckDB view of it. On
every engine, states and changes are added up by one plan Lean checks (a
union, grouped by every column, with the weights summed), so they group rows
as the model compares them: one NaN, `-0.0` equal to `0.0`, lists by their
elements. Sinks compute their change with the same plan (#173).

A view's rows, and what a sink writes, come in no particular order, as a
SQL query's do; before, they kept the order in which rows first appeared.

### Refreshes on DuckDB cost what changed

On DuckDB, a refresh no longer rebuilds a view's whole state. The merge plan
adds the change to the state rows it touches, and DuckDB replaces those rows
in place, in one transaction for every view: a refresh that changes ten rows
of a view of ten million costs about ten rows. Sinks write the sum of the
view's changes since the state they wrote. A view whose new contents a
recomputed view or `refresh(audit=True)` reads first is still merged in full
(#173).

### Delta and Iceberg tables read natively by DuckDB

On DuckDB, a `DeltaSource` or `IcebergSource` is no longer loaded into
Python. The pipeline holds the Parquet files of the table's version, chosen
by sverify's own pruning (#81, #108), with the rows that deletion vectors or
position delete files remove, and DuckDB reads them with `read_parquet`.
Refreshes keep the table as the files of the new version. Partitioned tables,
Delta column mapping, renamed Iceberg columns, equality deletes, object
stores and the other engines read through Arrow as before.
`scripts/bench_io.py` measures reading, refreshing and writing at scale (#173).

### The reference is a relation: an engine returns an allowed result or raises

`docs/reference-semantics.md` now defines correctness through the set of
results the reference allows for each input (`Rel.Allowed`,
`core/Sverify/Core/Allowed.lean`). The set holds more than one result where the
reference leaves a choice to the engine: the order of rows and of ties,
`FIRST`/`LAST` and `distinct(on=)` without an order, the order in which a double
`SUM` or `AVG` adds (#85), and the statistical aggregates. `Rel.eval` is one
allowed result (`Rel.eval_allowed`); a plan without choices allows only its
rows (`Rel.allowed_perm_eval`); rewrites are refinements (`Rel.Refines`); and
the DuckDB shim and guard elimination return allowed results. The page also
lists where the reference overrides Substrait (one zero, one NaN, the size
hypothesis), states principle 3 as "Every engine can follow it with reasonable
effort", and notes that `fp32` arithmetic is refused until #417.

### Integer overflow is an error at the declared width

Breaking: `+`, `-`, `*` and negation of integers whose result does not fit
its declared type (`BIGINT`, or `INTEGER`, `SMALLINT`, `TINYINT`) raise, on
every engine, where a plan omits `overflow` or asks for `ERROR` (#202). An
overflow `verify` cannot rule out makes the report unproved; it was a "may
wrap around" warning. Inferred bounds (#244) discharge most of these, and the
report's hint names the bound to add to `requires` for the rest. The
arithmetic sverify adds itself (0-based `row_number`, `find`, floor
division) is proved free of overflow, under the hypothesis that a window
reads fewer than 2⁶² rows (#254).

### An integer `SUM` that may overflow is an assumption checked on the data

`verify` no longer treats a possible integer `SUM` overflow as a warning. Where
the plan bounds a group's rows (a `VALUES` list, a `FETCH` count, an aggregate
without groups) and `requires` bounds the column, the overflow is ruled out.
Elsewhere sverify assumes each sum fits 64 bits, as it assumes inferred bounds
(#244), and lists it in `Report.assumed`; the SQL it writes checks it on the
data while the job runs. With `infer=False` it is an error that makes the
report unproved. A row cap (`sv.max_rows`, #219) discharges it statically. A
window `SUM` or `AVG` whose frame may hold both `+inf` and `-inf` is now
reported as a domain error, as the grouped one is (#257).

### A double divided by zero raises

`x / y` and `x % y` on doubles raise on a zero divisor, as on integers, when
the plan omits `on_division_by_zero` or asks for `ERROR` (#204). `verify`
reports "division by zero" unless the plan rules it out (`y > 0` in
`requires`, a filter, `NULLIF(y, 0)` or `CASE WHEN y <> 0`). A plan that asks
for `IEEE`, `LIMIT` or `NULL` gets that. Under `semantics="duckdb"`, SQL
divides as DuckDB does, giving `±inf` or NaN.

### Fixed: aggregates of double constants, casts between dates and timestamps

The reference computed two kinds of plans wrongly (#201). An aggregate of a
double constant read the constant as an integer: `SUM(CAST('inf' AS
DOUBLE))` is now `inf`, and `avg(42) OVER ()` is `42.0` (#205). A cast
between a date and a timestamp kept the number of days or microseconds: a
date now becomes midnight of that day, and a timestamp rounds down to its
day, before 1970 too. A comparison of a date with a timestamp without a cast
is refused (#206).

### Lists compare element by element

`<`, `>`, `ORDER BY`, `MIN` and `MAX` on lists order them lexicographically,
a proper prefix first (#207). A NULL element that decides a comparison makes
it NULL (`[1, NULL] < [1, 3]`); in `ORDER BY`, `MIN` and `MAX` NULL elements
sort after every other value
([reference semantics](../docs/reference-semantics.md)).

### Arithmetic on `FLOAT` (fp32) is refused

The reference computed `FLOAT` arithmetic in doubles, so `2e38::FLOAT / 0.1`
gave `2e39` where every engine gives `inf`. Arithmetic on `FLOAT`s and casts
to `FLOAT` are refused until binary32 is modelled (#208, #417). Reading a
`FLOAT` column, comparing it and widening it to `DOUBLE` are exact and keep
working; cast to `DOUBLE` first to compute with it.

### `avg` of integers follows the plan's output type

An `avg` of integers whose plan declares an integer result, as Substrait's
`avg` of `i64` does, is the exact mean truncated toward zero; a declared
`fp64` result is the mean as a double (#209). Other output types are refused.

### `substring` counts a negative start from the end

A plan that omits `negative_start` counts a negative start from the end of
the string, as DuckDB does: `substring('hello', -2, 2)` is `'lo'` (#209).
A plan that asks for `LEFT_OF_BEGINNING` gets that, and `ERROR` is refused.
The SQL writers and Polars rewrite the start before calling the engine's
`substring`.

### SQL strings are DuckDB's SQL, through sverify's own lift

`sv.sql`, `sv.verify` of a SQL string, SQL conditions in contracts, Ibis's
`Table.sql` and `Backend.sql`, and `sverify.engines.substrait_json` now read
**DuckDB's SQL** and plan it with sverify's own SQLGlot lift
(`sverify.sql_lift`, #239). DataFusion's SQL planner is gone as a frontend
(#211); DataFusion stays an execution backend (`engine="datafusion"`), and SQL
strings no longer need the `datafusion` extra.

This changes what some SQL means. In DuckDB's SQL, `/` divides as doubles
(`7 / 2` is 3.5; integer division is `//`), `1.5` is a `DECIMAL(2, 1)` rather
than a double, and NULLs sort last in both directions. A double divided by
zero raises under the reference semantics, the default (#411), and is `±inf`
or NaN with `semantics="duckdb"`. The entries for #240 list what the lift
reads; anything else is refused, saying what. Write those queries in Ibis
meanwhile.

### Row caps prove integer SUMs fit

A row cap `sv.max_rows(n)` in `requires` now proves integer `SUM`s fit 64
bits (#219): a `SUM` of values in `[-m, m]` over at most `n` rows, with
`n · m < 2⁶³`, is no longer an assumption checked on the data
(`Report.assumed`). Lean carries the caps through filters, unions, limits,
aggregates and joins. A join on a `unique` key of its right side keeps the
left side's rows (`Rel.capJoins_eval`), where a product would be far too
large. Caps are now:
- proved from the record counts of a Delta or Iceberg table's files;
- checked on every batch of an incremental view;
- proved in `ensures`.

`Report.rows` bounds the output's rows, and the SUM hint names the cap that
proves a sum fits.

### Casts between doubles, decimals and integers keep their bounds

- `CAST(x AS DECIMAL(p, s))` of a double whose bounds are known no longer
  reports a failed cast or a precision overflow when the casts of the bounds
  fit: after `WHERE f BETWEEN 0 AND 100`, `CAST(f AS DECIMAL(10, 2))` is safe
  (#223).
- `CAST(d AS DOUBLE)` of a decimal keeps the decimal's bounds, as
  `CAST(n AS DOUBLE)` of an integer already does. TPC-H Q08's contract is now
  proved, and Q14's division can no longer be by zero.
- The reference computes these conversions exactly (the nearest double,
  halves to even; `round(x · 10ˢ)` in doubles for the cast to a decimal) and
  states what they keep: monotone, within `2⁻⁵³` relatively, exact for
  integers up to `2⁵³`, which survive the round trip to a double and back.

### Benchmark catalogue refreshed for 0.4.0

The catalogue's 54 benchmark queries were probed again on 0.4.0. 53 are accepted and 53 now have a contract, of which 46 are proved and 49 run as verified SQL on DuckDB (#229). New contracts: TPC-DS q27 and q36 (ROLLUP lifts since #306) and H2O groupby q9 (`corr`). A query written in SQL now states its contract as SQL conditions.

TPC-H q11, q14 and q20 state row caps from the specification's largest scale factor. Each query still short of proved or verified SQL says why in its TOML, with the issue that would close it: SUMs bounded by row caps (#470), RANK over a ROLLUP (#471), keys through a FULL JOIN (#472) and ROW_NUMBER filters projected past their ties (#473).

### The SQL written for DuckDB is proved to return the reference's rows or raise

`Rel.duckdb_shim_sound` (`core/Sverify/Core/Profile.lean`) proves that DuckDB,
running the SQL sverify writes, returns `Rel.eval`'s rows or raises, for any
plan, with no contract needed (#185). Engine profiles state what DuckDB
computes for each function, and where it differs from the reference the
written SQL compensates ([engine profiles](../docs/engine-profiles.md)). The
query catalogue records, for each benchmark query, whether it is verified SQL
on DuckDB (`verified_sql` in [`catalogue/INDEX.md`](../catalogue/INDEX.md),
#229).

### Plans with `NOT IN` subqueries and decimals are written

A plan with DECIMAL arithmetic is written for the engines only if it reads
back as the same plan. A `NOT IN (subquery)`, or a `CASE` of several
branches, grew on every reading, so such a plan stopped at "this decimal
arithmetic cannot be written for the engines yet" (#238, TPC-H Q16's
shape). It is written now.

### `AVG` of a DECIMAL as a double

DuckDB SQL that averages a DECIMAL column, such as TPC-H Q1's
`avg(l_quantity)`, is now verified. DuckDB returns a DOUBLE, and so does
the plan: the exact sum, converted to a double, divided by the count. NULL
without values. Over windows it is still refused.

### Plans with decimals and a negated double are written

A plan with DECIMAL arithmetic is written for the engines only if it reads
back as the same plan. Negating a double, or taking its `ABS`, broke that,
so such plans (TPC-DS q89, for one) stopped at "this decimal arithmetic
cannot be written for the engines yet". They are written now.

### The SQL lift reads dates and timestamps

The SQL lift now reads dates and timestamps (#240): `EXTRACT`, `date_part`,
`year()` and its kin, `DATE - DATE`, `datediff('day', …)`, `date_trunc` of
a date, and a date or timestamp plus or minus a constant interval. Adding
months clamps to the month's last day, as in DuckDB. DuckDB types
`DATE ± INTERVAL` and `date_trunc` of a date as TIMESTAMPs. They compare
exactly with dates, but as an output column or next to a timestamp column
they need a cast of a date column to a timestamp the model lacks yet, and
are refused.

### The SQL lift reads GROUPING SETS, ROLLUP and CUBE

The SQL lift now reads `GROUP BY` with `GROUPING SETS`, `ROLLUP` and `CUBE`, alone or next to plain keys, and `GROUPING(…)` in the select list, HAVING, ORDER BY and window functions (#240). Each grouping set becomes its own aggregate, with NULL for the keys the set leaves out and the value of each `GROUPING(…)` as a constant. The aggregates are joined with `UNION ALL`, as DuckDB computes them. On empty input, the empty set's grand-total row is kept.

Two fixes came with it:
- A window function's `PARTITION BY` and `ORDER BY` may now be expressions, not only columns. The plan computes them as columns first, since the model reads them as columns.
- In an `ORDER BY` expression, a bare name is the output column of that name, as in DuckDB. For example, `ORDER BY CASE WHEN s > 0 THEN customer END` where `s` is an alias.

TPC-DS q27 and q36 now pass: 51 of 54 benchmark queries agree.

### The SQL lift refuses joins it would have read wrongly

The sqllogictest replay found queries the SQL lift read wrongly (#240). It now refuses them instead:
- **`ASOF JOIN` and `POSITIONAL JOIN`:** the lift read these as the inner join of their `ON`, or as a cross join. An ASOF join keeps each left row's latest match; a POSITIONAL join pairs rows by position.
- **`t.*` with `JOIN … USING`:** SQLGlot leaves the `USING` columns out of the right table's `t.*`, where DuckDB keeps them. `SELECT *` and listed columns still work.
- **Ordering comparisons (`<`, `<=`, `>`, `>=`) of structs:** DuckDB orders them field by field, with NULLs last, and the model's order differs. Lists still compare as DuckDB's, and equality still works.

Other queries the replay found read wrongly are refused or fixed too:
- **Clauses SQLGlot attaches to a table:** `TABLESAMPLE`, `PIVOT`, and the comma joins of a FROM-first query (`FROM a, b SELECT …`) are now refused. The lift used to read only the table and drop them.
- **Numbers with an underscore not between two digits** (`1__2`, `1._5`): DuckDB reads such an underscore as the start of an alias, SQLGlot as a digit separator (upstream/LEDGER.md SG-4). These are refused.
- **A constant that doesn't fit its cast's type** (`200::TINYINT`, `12.5::DECIMAL(2,1)`): the lift now writes the cast instead of an out-of-range literal. A string read as a decimal is read exactly, so `'1e38'::DECIMAL(38,0)` no longer goes through a double.
- **INTERVAL output columns:** these are refused, because the model holds intervals as microseconds while DuckDB keeps months and days apart.
- **Casts to the `NULL` type:** refused.

### The SQL lift reads numeric functions, DISTINCT and FILTER in aggregates

The SQL lift now reads (#240):
- **Numbers:** `power` (`**`, `pow`), `abs`, `round`, `floor`, `ceil`, `sign`, `isnan`, `greatest`, `least`, `nullif`, and `sqrt`, `exp`, `ln`, `log`, `log2`, `log10`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`.
- **Comparisons:** `IS [NOT] DISTINCT FROM`.
- **Aggregates:** `DISTINCT` in every aggregate, and `FILTER (WHERE …)`.

They have DuckDB's meanings:
- `power` and the elementary functions compute in doubles;
- `log(x)` is base 10;
- `greatest` and `least` leave NULLs out;
- `sign` is a TINYINT, 0 for NaN;
- `isnan(NULL)` is NULL.

Outside their domain (`sqrt(-1)`, `ln(0)`), DuckDB gives NaN or `-inf`. The plan states that preference and then `ERROR`, the reference's, which the model takes, so `verify` reports such rows as possible errors.

### The SQL lift reads strings

The SQL lift now reads strings (#240): `length`, `substring`/`substr` (from
1; a negative start counts from the end), `trim`/`ltrim`/`rtrim` (spaces,
or the characters given), `strpos`/`instr`/`position`, `contains`,
`starts_with`, `ends_with`, `prefix`, `suffix`, `LIKE`/`ILIKE` and their
`NOT`, `||`, `concat` (which leaves NULLs out), `replace`, `repeat`, `left`,
`upper` and `lower`. A LIKE pattern must be a constant without a backslash:
DuckDB's LIKE has no escape character, and the model's has one. `reverse`
is refused, because DuckDB reverses grapheme clusters.

### The SQL lift reads CTEs, subqueries and more joins

The SQL lift now reads (#240):
- **CTEs:** non-recursive `WITH`, inlined where each is read; a later CTE may read an earlier one.
- **Uncorrelated subqueries:** a scalar subquery (the checker must prove it has at most one row: an aggregate without groups, or `LIMIT 1`), `x [NOT] IN (SELECT …)` with SQL's rules for NULLs, and `EXISTS (…)`.
- **More joins:** `SEMI`, `ANTI`, `RIGHT` and `FULL` joins.

A subquery that reads a column of the query around it (a correlated subquery) is refused, saying so; write it as a join, or as a `SEMI` or `ANTI` join.

### The SQL lift reads window functions

The SQL lift now reads window functions (#240):
- **Ranking:** `row_number`, `rank`, `dense_rank`, `percent_rank`, `cume_dist` and `ntile`.
- **Values:** `lag` and `lead` (a constant offset, and a default), `first_value`, `last_value` and `nth_value`.
- **Aggregates:** `sum`, `avg`, `count`, `min` and `max` over a window, including windows over a query's aggregates (`rank() OVER (ORDER BY sum(x))`).
- **Frames:** `ROWS` and `RANGE` frames with integer offsets, and DuckDB's default frame: to the current row and its peers with an `ORDER BY`, the whole partition without.

`ntile` is DuckDB's, the SQL standard's buckets: 6 rows in 4 tiles are 1 1 2 2 3 4. The lift writes it from `row_number` and `count`, because the model's own `ntile` is DataFusion's. Named windows (`WINDOW w AS …`), `GROUPS` frames, `EXCLUDE`, `IGNORE NULLS` and `DISTINCT` in a window are refused.

### `NTILE` deals out buckets as SQL does

`NTILE(k)` now follows the SQL standard, as DuckDB, Spark and Snowflake
compute it: the first `n % k` buckets hold one row more. It used to follow
DataFusion's formula, which spreads the larger buckets out (`ntile(4)` of
10 rows gave `1 1 1 2 2 3 3 3 4 4`; now `1 1 1 2 2 2 3 3 4 4`). DataFusion
is refused for `NTILE` for now. `verify` still proves `1 ≤ NTILE ≤` the
row's number.

### The DuckDB replay's ledgers come from the SQL lift

`characterization/duckdb/*.json` now record the sqllogictest replay through the SQL lift on `main`, with #338's fixes (#240). Over 121 areas and 46,283 queries: 8,449 agree, 265 disagree, 22,931 refused, 14,638 skipped. The README's summary table is regenerated.

The replay itself:
- logs queries slower than 10 s;
- writes its summary table again: it no longer fails on `probes.json`.

Two lift regressions from #338 are fixed:
- A string read as a decimal rounds half away from zero past the scale, as DuckDB does, instead of being refused.
- A double constant is folded into a decimal where the decimal holds it exactly (`1e1::DECIMAL(38,0)`).

### `AVG` of a DECIMAL over a window as a double

`avg(d) OVER (...)` of a DECIMAL column in DuckDB SQL is now verified, as a
DOUBLE the way DuckDB types it, and arithmetic with it is in doubles (as in
TPC-DS q89's `sum_sales - avg_monthly_sales`).

### DuckDB's SQL writes the proved lowering

Where DuckDB computes a function differently from the reference, the SQL
sverify writes for DuckDB is now the template the Lean build generated and
proved (`substrait-check --lowering-table`, read by `sverify.sql.lowering`):
the guards for NaN and ±inf, the elementary functions' domains, division and
`%` by zero, `MIN % -1`, `<<`, and `overflow` = `SILENT` or `SATURATE`. The
hand-written versions in `sverify.sql.duckdb` are gone. Polars no longer
raises on a shift of NULL by an out-of-range amount, which the reference
leaves NULL (#241).

### Integer overflow can wrap around or clamp when a plan asks

A plan may now set `overflow` to `SILENT` (wrap around) or `SATURATE` (clamp)
on integer `add`, `subtract`, `multiply` and `negate`, at the declared width
(`i8` to `i64`); before, these were refused (#255). Nothing raises for them,
so `verify` reports no overflow. DuckDB runs them in 128-bit arithmetic, with
templates the Lean lowering generator found and proved (`SATURATE`) or a
hand-written, proved schema (`SILENT`); the other engines refuse them for now
([#241](https://github.com/AlexanderNenninger/substrait-lean/issues/241)).

### DuckDB's functions probed for the options they implement

`substrait-check --outcomes` evaluates each row of a projection over `VALUES`
under the reference and prints the value or the error raised. The maintainer
tool `python -m sverify_dev.probe` uses it to run DuckDB's arithmetic and
elementary functions on edge cases under every combination of
`error_on_division_by_zero` and `ieee_floating_point_ops`, and to keep the
Substrait options whose outcomes match
(`characterization/duckdb/probes.json`, FACTS R15). It corrected two facts:
double division by zero is IEEE under DuckDB's defaults, and `MIN % -1`
raises (#242).

### DuckDB's profile says what DuckDB computes, and the lowering compensates

`Profile.duckdb` now states DuckDB 2.0's behaviour where the probes found it
differs from the reference: NaN for operations on doubles that have no value
(`∞ - ∞`, `0 · ∞`, `∞ / ∞`, `sqrt(-1)`), `-∞` for a logarithm of 0, IEEE
division by zero for doubles (`ieee_floating_point_ops`, a new setting),
`atan2(0, 0) = 0`, `MIN % -1` raising, and the shifts. The generated lowering
to DuckDB guards each of them, every guard proved by the kernel, and
`Rel.duckdb_sound` is restated for DuckDB's IEEE mode, with the SQL printer
trusted for `MIN % -1` and `<<`, which it writes out. The lowering generator
keeps its results in `SubstraitLean/LoweringCache.lean`
(`substrait-check --lowering-cache`), so builds try each known template first
(#242).

### Engine facts as JSON documents, with provenance

What DuckDB does, judged against the reference semantics, is now one JSON
document per finding in `characterization/duckdb/facts/`, in the format of
`characterization/fact.schema.json`: the engine version checked, what the
engine and the reference do, a status, and each check's date, method, tool
and evidence (DuckDB's tests at their commit, the replay ledgers, the probe
verdicts of `probes.json`). DataFusion 51's findings from the replay are in
`characterization/datafusion/facts/`. `characterization/<engine>/FACTS.md`
is generated from them by `python -m sverify_dev.facts --write`.

### Inferred bounds against overflow

Contracts no longer have to state the bounds that rule out integer overflow
(#244). For `amount * 2` on a `BIGINT`, sverify infers `_.amount < 2**62`,
proves the contract with it, and treats it as a precondition: it is checked
on the data at call time and on every refresh, or proved from Delta and
Iceberg file statistics, and reports list it as inferred. The inference
covers `+`, `-` and `*` with constants or bounded columns, negation, `abs`,
narrow integers and timestamp truncation (#379), through projections,
filters, joins and `MIN`/`MAX`. Lean proves the contract again with the
inferred bounds, so a wrong inference only fails the proof. Where no single
bound exists (the product of two columns, a `SUM`, a value from another
contracted transformation), the report's `Issue.hint` suggests one.
`@sv.transform(infer=False)` and `sv.verify(..., infer=False)` require
explicit bounds.

### Inferred preconditions for more runtime errors

Sverify now infers preconditions for runtime errors besides integer
overflow, as #244 does for overflow. Each is the weakest per-column
condition, marked "(inferred)", checked on the data or proved from metadata,
and switched off by `infer=False`:
- division and remainder by zero: `(_.b != 0)`;
- domain errors: `sqrt`, logarithms, `asin`/`acos`, a fractional power;
- casts out of range: to narrower integers, and from doubles to `BIGINT`;
- `repeat` counts;
- decimal precision of `+`, `-` and `*`;
- date arithmetic.

Where no single bound exists (`∞ / ∞`, `substring` offsets counted from
either end, the sum of two unbounded decimals), the hint suggests one and
nothing is assumed ([docs/how-to-bounds.md](docs/how-to-bounds.md#inferred-bounds)).

### Suggested preconditions for unproved postconditions

An unproved postcondition that compares a value with a constant now comes
with the precondition on the inputs under which it holds: `_.doubled <= 100`
with `doubled = qty * 2` reports "would hold with `(_.qty < 51)` in the
requires of 'items'". Sverify proves each suggestion before showing it and
never assumes one. `CheckedCondition.suggested` and `Report.suggestions`
carry them as code, for editors and language servers (#291).

### Decimals in reports keep their scale

`verify`'s "known about the output" showed a decimal column's bound as its
internal unscaled integer: TPC-H Q6's `revenue` read "an integer ≥ 450000".
It now reads "a decimal(38, 4) ≥ 45.0000", with the column's type (#250).

### Dates: the reference's own range

Date arithmetic is now checked against the reference's dates, the SQL
standard's 0001-01-01 to 9999-12-31, instead of the (much wider) range
DataFusion computes. Adding days or months that leaves them raises "outside
the reference's dates" on every engine, and `verify` reports it. With
constant operands, such as TPC-H Q6's `DATE '1994-01-01' + INTERVAL 1 YEAR`,
the written SQL no longer carries a range check at all (#251).

### More divisors proved non-zero

`verify` now proves a divisor non-zero from more preconditions:
`(b < 0) | (b > 0)`, `(b != 0) | b.isnull()`, and a product `b * c` of
factors each known to be non-zero. Each needed a guard before.

### What DuckDB SQL lifts to is generated and proved

The Lean build now generates, for DuckDB's `/` (of integers and of doubles),
`%` of doubles, `log`, `sign`, `greatest` and `least` (which skip NULLs) and
casts between BIGINT and DOUBLE, and the aggregate `avg` of BIGINTs, the Substrait expression each lifts to under
`semantics="duckdb"` and `"reference"`, and proves it means what DuckDB's
function means (`SubstraitLean/DuckDBSQL.lean`, `LiftSearch.lean`). With
DuckDB's semantics, `±∞` and NaN results are stated exactly, as guarded
constants: `log(0)` is `-∞`, `x % 0.0` is NaN. `substrait-check --lift-table`
prints the table as JSON, for the SQL lift to read; a function the model
cannot state is listed as refused, with the reason (DuckDB's `CAST` of a double
to an integer rounds half to even)
([#268](https://github.com/AlexanderNenninger/substrait-lean/issues/268)).

DuckDB's `avg` of integers sums them exactly before dividing; with DuckDB's
semantics it now lifts to `CAST(sum(x) AS DOUBLE) / count(x)`, proved equal,
where Substrait's `avg` of doubles would round as it sums (values beyond 2⁵³).

### DuckDB's elementary functions and power lift exactly, and the lift has a cache

With `semantics="duckdb"`, `sqrt`, `exp`, `ln`, `log`/`log10`, `log2`, the
trigonometric functions and `power` now lift to what DuckDB computes, NaN and
`±∞` included (`sqrt(-1)` and `asin(2)` are NaN, `ln(0)` is `-∞`, a negative
base to a fractional power is NaN), each proved
([#268](https://github.com/AlexanderNenninger/substrait-lean/issues/268)). The
lift generator keeps a cache of the templates it found
(`SubstraitLean/LiftCache.lean`, regenerated with `substrait-check
--lift-cache`), tried first on the next build: a build with the cache takes
15 s where a search from scratch takes about 3 minutes. A template the search
does not reach can be seeded by hand there; it is still proved by the kernel.

### The SQL lift reads Lean's generated DuckDB lift table

With `semantics="duckdb"`, the SQL lift now writes what Lean's generated lift table says for each construct it covers (#268): `/`, `%` of doubles, `log`, `sign`, `greatest` and `least`, casts between BIGINT and DOUBLE, and `avg` of integers. Lean generates each entry and proves it means what DuckDB computes. `substrait-check --lift-table` exports the table, and the lift reads it from the checker sverify ships with.

The entries state NaN and ±inf exactly, as DuckDB computes them, instead of refusing them or raising:
- `%` of doubles is no longer refused: by zero, or of an infinity, it is NaN.
- `log(0)` is `-inf`, and `log` of a negative is NaN.
- `inf / inf` is NaN.

A contract that NaN or an infinity would break fails to prove, and one they can't break still proves. `avg` of integers is the exact sum divided by the count, in doubles, as DuckDB computes it.

The other constructs keep their hand-written rules until their entries are generated. The reference semantics is unchanged.

### Decimals

`DECIMAL(p, s)` columns, literals and arithmetic are verified, in Ibis and in
SQL (#27, #67). The reference computes them exactly: `+` and `-` at the
larger scale, `*` at the sum of the scales, and an overflow of the precision
is an error, which `verify` rules out from the columns' declared precision.
Casts to a smaller scale round half away from zero, to an integer truncate,
and to and from doubles round once. `SUM`, `MIN`, `MAX` and `AVG` work in
groups and windows; `AVG` is `DECIMAL(p + 4, s + 4)`, rounded half away from
zero. Division of decimals is refused. DuckDB runs decimal plans and
compensates where its own types or rounding differ
([engine profiles](../docs/engine-profiles.md)); Polars, Spark and Snowflake
refuse them for now.

### Chapter 16 of the tour folded into chapter 17

The tour's appendix on DataFusion's quirks (`16_datafusion_semantics.py`)
described DataFusion as the SQL frontend it no longer is (#211). Its parts
that still matter now live in chapter 17 (`17_backend_semantics.py`), as a
new section 8 on DataFusion as a backend: when DataFusion evaluates an
expression (E1–E5), and the soundness gaps found while sverify planned SQL
with DataFusion (D1–D11), each re-checked live against `verify` and the
model and ranked most severe first. Most of those gaps closed with the lift;
what remains is that DataFusion wraps integer overflow silently where the
model raises, which `verify` reports as `may fail: overflow`.
`catalogue/pitfalls.toml`'s `quirks` now name chapter 17's entries.

### DuckDB is the test oracle; the docs describe SQL as DuckDB SQL

The tests check the reference model and the engines against DuckDB, the Tier 1
engine, wherever they used to run raw SQL or Ibis's SQL on DataFusion as an
oracle. DataFusion keeps the tests about it as a backend: checked plans
running on it, and the native behaviours that motivate a refusal.
`sverify.engine.run_sql` (internal) is gone. Raw DuckDB SQL over a
connection's tables is `sverify.testing.duckdb_sql`, and an Ibis expression's
own DuckDB SQL is `sverify.testing.duckdb_ibis`. The coverage harness's
`DATAFUSION_SQL` and `NO_DATAFUSION_SQL` are replaced by one list,
`NO_DUCKDB_SQL`: the cases where DuckDB's own SQL computes something other
than the plan. `sverify.testing.parse_row` is private now (`parse_rows`
stays). The README, `python/README.md`, `docs/reference-semantics.md`, the
tour's chapters 12 and 14 and the agent skills describe SQL as DuckDB SQL,
read by sverify's lift with `semantics="duckdb"` or `"reference"`, and
DataFusion as an optional backend.

### Bounded state for time buckets: `arrives_within` and retention by watermark

`sv.arrives_within("ts", hours=2)` in `requires` bounds how late a source's
rows arrive. It is checked on every batch at refresh: a row before the
watermark (the largest `ts` seen minus the lateness), or a NULL, rejects the
batch. A node that aggregates by `ts.truncate(...)` or `ts.bucket(...)` then
drops the buckets that end at or before the watermark from its state once its
sink has written them, and keeps at most `⌈lateness / width⌉ + 1` open. Lean
proves that a final bucket's delta is empty for every admissible batch and the
bound (`SubstraitLean/Retention.lean`). The refresh report gives the open and
retired buckets and the bound. `DeltaSink` keeps the retired buckets
(`Sink.keeps_retired`); with other sinks the node keeps every bucket (#294).

### The last of DataFusion's SQL path is gone

sverify no longer monkey-patches Ibis's DataFusion SQL compiler: the two
patches (sub-second interval literals, integer `//`) changed Ibis for every
user of Ibis-on-DataFusion and served only the internal
`sverify.engine.to_sql`, which is removed as well. The one `to_sql` left is
`sverify.engines.to_sql`, which writes SQL from a checked plan. The query
catalogue runs each query on DuckDB itself rather than DataFusion
(`status.json` records it as `native`), and no longer asks DataFusion's SQL
planner whether a query plans.

### Integer division overflow at narrow widths

`MIN // -1` at TINYINT, SMALLINT and INTEGER (`-128 // -1` is 128, which a
TINYINT cannot hold) is now reported as an overflow, as it already was for
BIGINT, and the plans sverify writes raise there, as DuckDB does (#334).
Integer division at a narrow width is now checked at that width, like `+`,
`-`, `*` and negation. The sqllogictest replay also sees `verify`'s warnings
for queries that read no table, such as `SELECT 7 // 0` (#333): `verify`
reported those all along, but the replay's check went through
`sverify.sql`, which refuses such queries.

### `round(x, d)` at every number of digits

`round(x, d)` of a double now means what DuckDB computes for every `d`
(#335): below zero it divides by an exact power of ten and multiplies back,
so `round(42.0, -1000)` is 0, not NaN, and `round(521924.889, -5)` is
`500000.0`, not `499999.99999999994`. A result that would not be finite
falls back to 0 (for `d < 0`) or to `x` (for `d ≥ 0`). The plans sverify
writes now include `round` with digits for a double literal, which they
refused before ("unsupported function round/2"). DataFusion rounds
otherwise, so it refuses `round(x, d)` until #271.

### `substring` out of range is an error, and strings have fewer than 2³² characters

- The size hypothesis for strings is now 2³² characters (it was 2⁶²); relations
  a window reads keep 2⁶² rows (#336).
- `substring` with an offset outside `[-2³², 2³²)` or a length of `2³²` or more
  is an error in the reference semantics, as DuckDB raises. `verify` reports it
  as a domain error unless the offset's bounds rule it out, for columns and
  constants alike, and the written plans raise there on DuckDB and Polars. The
  lift no longer refuses such constants.

### GREATEST and LEAST check in linear time

`GREATEST(a, b, c, …)` and `LEAST(…)` used to be read as a chain of conditionals, each of which copied the one before. With ten arguments, the checker ran for minutes, and a plan written back held thousands of copies of each argument (#340). They're now one operation per pair, `BinFn.greatest`/`least`, which `Expr.eval_greatest` proves is the conditional it replaces. Thirty arguments check in well under a second.

The contract checker keeps its precision. `GREATEST(x, 0)` is still known to be at least 0, and Ibis's `clip` to stay within its bounds; `pickAbs` is proved sound. Written plans carry `greatest`/`least` as single calls, run natively:
- DuckDB, Spark and DataFusion: their own `GREATEST`/`LEAST`, which skip NULLs;
- Snowflake: `GREATEST_IGNORE_NULLS`;
- Polars: the same comparison as before, now one step per pair.

Greatest and least of lists are written as the conditional, as before.

### Set operations in SQL

DuckDB SQL with `UNION`, `EXCEPT` and `INTERSECT`, each with or without `ALL`,
now verifies, in subqueries and CTEs too, with `ORDER BY` and `LIMIT` over the
whole operation (#344). The branches meet at DuckDB's common column types, and
take the first branch's names. NULLs count as equal, and with `ALL`, `m` and
`n` copies of a row leave `min(m, n)` (`INTERSECT ALL`) or `max(m − n, 0)`
(`EXCEPT ALL`), as in DuckDB. DuckDB's `TABLE t` shorthand, which SQLGlot does
not parse, is written out as `SELECT * FROM t` first. In the sqllogictest
replay, the `setops` area went from 18 agreeing queries to 79, none disagreeing.
`UNION BY NAME` is still refused.

### Windows over every column are deterministic

A window partitioned by every column of its input, such as
`ROW_NUMBER() OVER (PARTITION BY` every column`)`, is now reported as
deterministic without a key. Rows tied in such a partition are equal, so how
an engine breaks the ties cannot change the result (`window_allColumns`,
proved). So `INTERSECT ALL` and `EXCEPT ALL`, which number the copies of each
row this way, are deterministic too, with or without keys on their inputs.

### Lists in DuckDB SQL: literals, indexing, UNNEST

The SQL lift reads DuckDB's list literals (`[1, 2, 3]`, nested ones too),
`l[i]` with a constant index (from 1, from the end for a negative `i`, NULL for
`0` and out of range), and `UNNEST(l)` in the select list (one row per
element, none for a NULL or empty list) (#348). Lean's results match DuckDB's.
DuckDB's SQL writer has no lists yet (#94), so these plans are checked against
DuckDB's own result but not run back; the sqllogictest ledgers now count such
agreements apart ("Oracle A only"). Lists of computed elements, of DECIMALs,
slices and an untyped `[]` are refused with a reason.

### Contracts on rollups: `MIN`, `MAX` and `AVG` of a group

More of a rollup's contract is proved before any data runs.

- `MIN` and `MAX` of doubles are accepted (#371). DuckDB orders doubles as
  the reference does, `-∞ < … < +∞ < NaN`; Polars and DataFusion refuse them
  until #271.
- `MIN`, `MAX`, `AVG` and `SUM` of a column that is never NULL, over a group
  without a filter, are never NULL (#372).
- `MIN ≤ MAX` for measures of the same values on one group, and an integer
  `AVG` with an integer result lies between them (#372).
- A decimal `AVG` and an integer `AVG` with an integer result lie within their
  values' bounds (#237). TPC-H Q17's `0.2 * avg_qty` is now proved not to
  overflow.
- A conversion of integers to doubles keeps their bounds: `CAST(x AS DOUBLE)`
  of `x` in `[0, 1000]` is in `[0.0, 1000.0]`.

An `AVG` of doubles, including the mean of integers as a double, rounds and
can step past its values (the mean of three `0.1` is `0.10000000000000002`),
so it gets no bound from its inputs here. Error bounds for it come with #85.

### Runtime-checked postconditions on nodes

`on_unproved="runtime"` now works on nodes built from sources (#373). The
postconditions Lean could not prove are checked at every refresh, on the full
result the first time and then on the rows each batch inserts (keys on the
new state), before the sink commits. A violation raises `PostconditionError`
and the refresh writes nothing. Before, building such a node raised
`VerificationError`. The transform's report marks these postconditions as
checked on data (`CheckedCondition.checked`), and the refresh report lists
them as `ensures` lines next to the preconditions. Downstream transforms
assume only proved postconditions, so a node with checked ones is stored with
`.write` before another transform reads it. An incremental view of an eager
result checks them on every batch too.

### Custom sources resume from the cursor their sink recorded

A sink now records the cursor of each source next to its version
(`Contract.cursors`). A `sverify.io.Source` that implements
`restore(cursor)`, the whole table as of a recorded cursor, starts there
after a restart: the stored nodes resume from their sinks, the first
refresh reads only what is new since, and the sink writes that change.
`from_query`, `from_files` and `FlightSource` implement it. A source without `restore`, or
whose cursor is gone (`restore` returns None), is read in full again and
written once, as before. `Source.snapshot` also serves the versions whose
batches the source still keeps (#374).

### Arrow Flight sources

`sverify.io.flight.FlightSource` reads a table of a numbered batch log on an
Arrow Flight server: each refresh streams the batches after the last one
read, registers them with the engine without a copy, and reads the batches
the server dropped past its retention as deletes. `FlightLog` is a small
in-memory server for that log, and the [guide](docs/tasks.md) documents the
protocol for other servers. `pip install 'sverify[flight]'` (#375).

### A source with `schema=` proves contracts without reading

`Source.schema()` returns the schema given as `schema=` without reading the
source, so building a node proves the transform's contract whatever the state
of the source, and the first read happens at the first refresh (#376).

### Delta sinks maintain their tables and resume past maintenance

`DeltaSink` takes `checkpoint_interval`, `log_retention`, `compact_every`
and `vacuum_retention`, and `DeltaSink.maintain()` compacts and vacuums by
hand. The maintenance commits carry the contract of the sink's last commit.
A restarted job now resumes from a table whose commits after the sink's
last one change no rows: `OPTIMIZE`, `VACUUM`, property and constraint
changes, by `maintain` or another writer. It used to recompute the node and
overwrite the table. An Iceberg sink resumes past `replace` snapshots
likewise (#377).

delta-rs 1.6.6 hangs in `history()` and `set_table_properties()` against an
S3 server in the same Python process, such as moto's `ThreadedMotoServer`
(`upstream/LEDGER.md` DL-1). Run moto as its own process.

### One-line refresh summaries

`Refresh.summary()` gives one line per node for the log of a job that
refreshes often, such as "paid: orders@v1→v2, Δ trusted (change feed),
requires checked on 1 row(s) (3 proved from metadata), merge v3: +1 −0"
(#378). Postconditions a node checks on its output (`on_unproved="runtime"`)
show as "2 ensures checked on data", and a node's time buckets (#294) as
"bucket: 3/3 bucket(s) open, 1 retired". `str(refresh)` keeps the full report. A node's line becomes its full
entry when the refresh did something notable (`StageRefresh.notable`): its
first refresh, a source recomputed without a change feed, a schema change
(`SourceRefresh.schema`), or a sink overwriting its table.

### Overflow hints name the bound to add

A report's overflow hints now name the column and propose bounds (#379),
in `Report.hints` and as `hint:` lines. A truncated or binned timestamp or
date gets a lower and an upper bound on its column, such as
`_.ts >= datetime(2000, 1, 1)` and `_.ts < datetime(2100, 1, 1)`, which clear
the overflow. An integer `SUM` that is checked while the job runs gets the
range Lean knows for the column it adds up and the largest group whose sum
then fits 64 bits, or, for an unbounded column, a bound to add and the group
size it allows. No contract can state a group's size, so the hint says so.
The general hint stays for overflows the new ones do not cover.

### GREATEST and LEAST of date and timestamp constants run as dates again

`LEAST(DATE '1992-01-01', DATE '1991-01-01')` and its timestamp counterpart returned the integer code of the result on DuckDB (`7670`, `662693025000000`), whenever every argument was a constant (#381, a regression of #355). The plan Lean writes back now writes two constants in the call's own kind, as it does elsewhere, so they are dates and timestamps to the engines. Lean's own results were right throughout.

### TIME constants, substring ranges and retention under a projection

- `TIME '13:45:21'`, `CAST('…' AS TIME)` and a string compared with a `TIME`
  column now lift to a TIME literal, so queries that compare a `TIME` column
  with a constant verify. Constants DuckDB raises on, and `24:00:00`, are
  refused (#386).
- `substring` with a constant offset outside [-2³², 2³²) or a constant
  length of 2³² or more is refused: DuckDB raises there, and the model has
  no such error yet (#336).
- Retention engages for an aggregate under a filter or a projection, such as
  a per-mille-to-percent `select` after the `aggregate` (#394).

### `arrives_within` lets a source's own retention through

A delete before the watermark no longer rejects the batch when its row is in
a bucket every retiring view has made final: it is the source's own
retention, such as a `FlightSource` floor or a Delta `VACUUM`. The views and
their sinks keep those buckets, and the report counts the expired rows. Lean
proves the result is the full recompute over the rows the source received
(`Retention.expiry_sound`). A delete before the watermark in a bucket that is
still open rejects the batch (#395).

### Clearer contracts API and messages

- A `requires` key that names no input raises a `ValueError` naming the key,
  the inputs and a close match, where it raised a bare `KeyError`. A
  transformation with one input takes a plain list,
  `requires=[_.amount >= 0]` (#408).
- `@sv.transform(infer=False)` turns off bound inference, as on `sv.verify`.
  `strict=True` still works and warns that it is deprecated (#409).
- `sv.references("cust", to=customers.id)` names the referenced column with
  an Ibis column or a `(table, column)` pair. The positional form
  `references(col, table, other)` warns that it is deprecated (#412).
- `Connection.datafusion` is deprecated: the DataFusion session is an
  internal of the DataFusion engine (#413).
- Refusals give their reason in terms of the reference semantics, with the
  issue to follow and a workaround, and no longer cite DataFusion's
  behaviour (#410).
- An unproved condition says why in words: "it may be FALSE on some rows",
  and where it may be NULL, how to declare the column NOT NULL. This
  replaces "(it is TRUE or FALSE)"; `CheckedCondition.why` has the text
  (#176).

### The reference semantics is the default everywhere

Breaking: `sv.sql(query)` now uses sverify's reference semantics by default,
as `sv.verify` and `@sv.transform` do; DuckDB's semantics (NaN and ±inf as
DuckDB computes them) is an explicit opt-in, `semantics="duckdb"` (#411).
Write `semantics="duckdb"` on `sv.sql` calls that relied on the old default.
SQL transformations and SQL conditions in `sv.verify` and `@sv.transform`
were lifted with DuckDB's semantics too, and now follow the new `semantics=`
parameter of each, which defaults to the reference. `Report.semantics`, and a
`semantics:` line in the printed report, say which semantics a check used.

### Narrow arithmetic on constants keeps its width

In `(10::TINYINT * 10::TINYINT) * x`, the parser treated the inner product as
a 64-bit value because it reads no column, so the outer multiplication was
not checked at 8 bits: `verify` missed the overflow and the written plan
returned 1000 where DuckDB raises. A call's declared output type now gives its
width (#419), as a column's does, at TINYINT, SMALLINT and INTEGER and for
`+`, `-`, `*`, negation and division.

### Inferred bounds on eager tables

`@sv.transform` on an eager table (an `ibis.memtable`, or any plain Ibis
expression that is not a contracted result) now infers the bounds that rule
out overflow, checks them on the table's data, and proves the contract, as
`sv.verify` does. Hints name the bound as a `requires` of the parameter
([#430](https://github.com/AlexanderNenninger/substrait-lean/issues/430)).

### Fixed: `avg` of a nullable integer under `semantics="duckdb"`

An `avg` of an integer column that may be NULL failed its proof with
"division by zero", because DuckDB's `avg` is lifted as the sum divided by
the count, and the count of a group whose values are all NULL is 0. The lift
now states that such a group's average is NULL, as DuckDB returns it, so
nothing can fail (#434).

### Fixed: reports on a DATE beyond the year 9999

A transformation with a DATE column whose range passes Python's limits, such
as `CAST(ts AS DATE)` of a TIMESTAMP, raised `OverflowError` while describing
its facts. Bounds outside the years 1 to 9999 now go without saying: the
column is "any date" (#435).

### A transformation with an `ibis.param` says how to bind it

A contracted transformation whose body uses an `ibis.param` failed with a
bare `KeyError` from Ibis. It now raises a `TypeError` naming the parameter:
transformations don't bind parameters yet (#354), so prove the expression
with `sv.verify(expr, params={param: value})` or write the values as
`ibis.literal(...)` (#440).

### Fixed: Ibis's DuckDB `create_table` failed on a fresh install

A fresh install resolved SQLGlot 30.18 or later, from which SQLGlot reads a
`DROP`'s names where Ibis 12 doesn't put them, so `con.create_table(...)` on
Ibis's DuckDB backend raised a DuckDB syntax error. sverify now requires
`sqlglot~=30.17.0` until Ibis follows
([upstream/LEDGER.md](../upstream/LEDGER.md) SG-7, #442).

### Fixed: SQL reports described timestamps and dates as integers

The facts of a SQL transformation described its timestamp and date columns
as "any integer", the model's codes for them. They now read as the same
columns written in Ibis do, "any timestamp" and "a date in [...]" (#452).

### Numeric functions: `sqrt`, logarithms, trigonometry, `sign`, bitwise operations

Ibis's `sqrt`, `exp`, `ln`, `log`, `log2`, `log10`, `sin`, `cos`, `tan`,
`asin`, `acos`, `atan`, `atan2`, `cot`, `degrees`, `radians`, `sign`,
`isinf`, `e` and `pi`, and the bitwise `&`, `|`, `^`, `~` and shifts, are
verified (#48). The functions compute as C's libm does, and contracts treat
their results as doubles. Outside a function's domain (`sqrt` of a negative,
the logarithm of 0, `asin(2)`, `atan2(0, 0)`, a shift by more than 63) the
reference raises a domain error, which `verify` reports unless a filter or
`requires` rules it out: `t.filter(_.x > 0).select(_.x.ln())` is proved.
DuckDB and Polars run them all; Spark runs `sqrt` and the bitwise operations,
Snowflake `&`, `|` and `^`, and both refuse the rest.

### Regular expressions and digests

Ibis's `re_extract` and `re_replace` (DuckDB's `regexp_extract` and
`regexp_replace`, with or without the flag `'g'`) and `hexdigest('md5')` and
`hexdigest('sha256')` are verified on DuckDB (#50). Patterns must be
constants in the subset `Text.simpleRegex` accepts, which now includes
non-capturing groups `(?:…)`. Proofs treat these functions as black boxes,
but Lean evaluates them: regular expressions with RE2's leftmost-first
matching and DuckDB's edge cases (`''` where nothing matches, `\1` in the
replacement, empty matches), and the digests as lowercase hex. So
ClickBench Q28 and dbt's surrogate key now verify. DuckDB's `hash()` and
Ibis's URL parts (`host()`, …) are refused, and the other engines refuse
all of these until #271. The DuckDB SQL of `\b` in a pattern now raises on
non-ASCII text, as `\d`, `\w` and `\s` already did, since RE2 and Rust
disagree there.

### `any()` and `all()`

Ibis's `any()` and `all()` of booleans are now verified, as `MAX` and `MIN`
(`BOOL_OR` and `BOOL_AND`): NULLs are skipped, and a group without a
non-NULL value gives NULL (#53).

### Bit aggregates

`bit_and()`, `bit_or()` and `bit_xor()` of integers are verified: the
64-bit operation folded over the non-NULL values, NULL for a group without
one. They run on DuckDB, Polars, DataFusion, Spark (`BIT_AND`, …) and
Snowflake (`BITAND_AGG`, …) (#53).

### Covariance and correlation

Ibis's `cov()` and `corr()` (DuckDB's `COVAR_SAMP`, `COVAR_POP` and `CORR`)
are verified on DuckDB, grouped, with DuckDB's own algorithm (#54). `CORR`
is NULL for fewer than two pairs and where one side's values are all equal,
as the SQL standard says, rather than DuckDB's NaN, and an infinite value
raises, since a deviation from the mean would be NaN. The other engines refuse
them until #271.

### Variance and standard deviation

`var()` and `std()` of doubles and integers, of a sample or a population
(`how="pop"`), are verified on every engine (#54). Each engine uses its own
algorithm for now, so results may differ in the last bits, and a contract
can rely only on the value being a non-negative double, or NULL: for no
values, and for a sample of one value. A NaN passes through; an infinite
value raises, since its deviation from the mean would be NaN. Variances over
windows are refused.

### `distinct(on=)`, and `first()`/`last()` without an order

Ibis's `distinct(on=…)` and `first()`/`last()` without `order_by` (DuckDB's
`FIRST`/`LAST` with no `ORDER BY`) are now verified rather than refused
(#55). They take any row's value, so the report says the result is not
`deterministic`, and proves nothing about it, unless the grouping (`on`)
columns form a key. Each column is chosen on its own: `distinct(on="name")`
may keep `a` from one row and `b` from another, so a fact about every input
row, such as `a <= b`, need not hold of the result. They run on DuckDB for
now; the other engines refuse them until #271.

### `first()` and `last()` with an order

Ibis's `first(order_by=…)` and `last(order_by=…)` (DuckDB's `FIRST(x ORDER
BY …)`) are verified: the first or last non-NULL value in that order, NULL
without one (#55). Without `order_by` they are any row's value and stay
refused. Where rows tie in the order, the report says the result is not
`deterministic`, unless the grouping and order columns form a key. They run
on DuckDB for now; the other engines refuse them until #271.

### `group_concat()` with an order

Ibis's `group_concat(sep, order_by=…)` (DuckDB's `STRING_AGG(x, sep ORDER
BY …)`) is verified: the non-NULL strings in that order, joined by a constant
separator, and NULL without values (#55). Without `order_by` the order is
the engine's, so it stays refused. As for `first()` and `last()`, rows that
tie in the order make the report not `deterministic` unless the grouping and
order columns form a key. It runs on DuckDB for now; the other engines refuse
it until #271.

### `ibis.param` values for `verify`

`sverify.verify` takes `params={param: value}`, as Ibis's
`execute(params=...)` does, and binds each `ibis.param` to its value before
compiling (#58). The report is about the expression with those values, and
says so: `Report.params` lists them, and the report notes that its proofs
hold for those values only. A parameter left unbound is still refused, now
with a reason that says to pass `params`.

### Refusals say why

`random()`, `uuid()`, `now()`, `today()`, `typeof()`, `ibis.param` and
`try_cast` were refused with "X is not supported". The message now gives
the reason and what to do instead, for example to pass the time in as a
column or constant (#58).

### `try_cast()`

Ibis's `try_cast()` (Substrait's `failureBehavior: RETURN_NULL`, SQL's
`TRY_CAST`) is verified for a double to an integer and an integer to a
narrower integer (#58): NULL where `cast()` would raise, so `verify` reports
no "cast out of range" for it. A double still truncates toward zero, as the
reference's `cast()` does, where DuckDB's own `TRY_CAST` rounds. `TRY_CAST`
to a DECIMAL, of a DECIMAL to an integer, and of strings is refused. It runs
on DuckDB for now; the other engines refuse it until #271.

### Casts of rounded aggregates keep their bounds

With a row cap (`sv.max_rows`), a cast of a `SUM` or `AVG` of doubles keeps
the aggregate's proved error bound (#85, #223). `CAST(AVG(cpu) AS BIGINT)` of
`cpu` in `[0, 100]` is in `[0, 100]`, and `verify` no longer reports that the
cast may fail, nor a cast to a decimal that the bound keeps within its
precision. A `SUM` of integers cast to doubles carries each conversion's
rounding in its bounds.

### Contracts on `SUM` and `AVG` of doubles, up to rounding

Rollups of doubles get proved bounds (#85).

- `sv.max_rows(n)` caps an input's rows, checked on the data. With a cap, a
  `SUM` or `AVG` of doubles in `[lo, hi]` is bounded by the exact result's
  interval widened by the proved rounding error (`docs/float-bounds.md`).
- `sv.approx(cond)` states a postcondition up to that rounding:
  `sv.approx(_.cpu_avg <= 100)` is proved where `_.cpu_avg <= 100` is not,
  and runs as `_.cpu_avg <= 100.0001`. A report hints at it when an exact
  claim fails only by rounding.
- Signs are exact without a cap: a `SUM` or `AVG` of values `≥ 0` is `≥ 0`.

### Proved error bounds for floating-point aggregates

The `float-bounds/` package proves error bounds for `SUM`, `AVG`, `VAR_*`,
`STDDEV_*`, `COVAR_*` and `CORR` of doubles (#85), in the standard model of
rounding with its underflow term. A sum of `n` values is within
`γ n · Σ(|xᵢ| + 2⁻¹⁰²²)` of the exact one, sequentially or in shards; the
co-moment behind the variance family is within `64 · n² · u · B²` for each of
the two-pass, textbook and Welford/Chan algorithms (DuckDB's), so the bound
holds whatever an engine uses. See `docs/float-bounds.md`.

### Generic properties of statistical aggregates

`VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` now have proved generic properties
that any common algorithm keeps (#85): `NULL` where the reference says, a
variance `≥ 0`, the result within `(128 n² u B² + 12 n u B²) / d` of the
exact one, and `|CORR| ≤ 1 + ε` when both variances are bounded below. The
reference allows any result with them (`StatProps`), so DuckDB's Welford,
Polars' blockwise two-pass and the reference's own two-pass all agree with
it. Engine profiles can name a stricter algorithm (`Profile.statAlgo`).
A computed double's bound now carries through `CAST(x AS BIGINT)` with row
caps, and `SUM(CAST(x AS DOUBLE))` of integers gets the summation bound.
See "Statistical aggregates" in `docs/reference-semantics.md`.

### Statistical aggregates within bounds that scale with the spread

`VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` may now differ from the exact result
only by bounds that scale with the spread of the values (`StatProps`,
`docs/reference-semantics.md`). For `10⁶` values near `10⁶` that vary by about
`1`, the variance is within about `2 · 10⁻²`, where the earlier bound allowed
`1.4 · 10⁴`. The bounds are proved for two-pass and for DuckDB's algorithm;
the textbook formula `Σx² − (Σx)²/n` falls outside them.

### Variance bounds that scale with the spread

`float-bounds/` proves tighter variance bounds for three algorithms (#85):
two-pass, Lean's own, is within `8 n u S + 80 n² u² Σx²` of the exact sum of
squared deviations `S`, Welford's update within one thread within
`32 n u √(S Σx²) + 104 n² u² Σx²`, and DuckDB's parallel aggregation (Welford
in each thread, Chan's merge with a fused multiply-add) within
`148 n u √(S Σx²) + 3961 n² u² Σx²`. The covariance has the analogues, for
two-pass and for DuckDB's parallel aggregation, in `√(S_xx S_yy)`,
`√(Σx² S_yy)` and `√(Σy² S_xx)`. They stay useful for values far from zero
with a small spread, where the generic bound does not. The
standard model of rounding now states that a double rounds to itself.

### Lists run on DuckDB

Plans with lists now run on DuckDB as well as Polars (#94): list columns and
literals, list elements and `length`, `collect()` (ordered or not, NULLs
skipped) and `unnest`. The written SQL keeps Lean's order: each row's
elements come out in list order, and ties in a `collect` order fall to the
row order, so an order-dependent step above sees the same rows Lean does.
Snowflake and Spark still refuse lists, until #271; structs and lambdas stay
Polars-only for now.

### Struct fields, list elements and lambdas

Ibis's struct fields (`t.s.a`), list elements (`t.l[0]`, a constant index,
negative from the end), `length()` of a list, and `map`, `filter` and
`contains` on lists are verified (#94). A lambda may read only its element
and constants, so `contains(v)` needs a constant `v`. A NULL element matches
only NULL in `contains`. `verify` reports an error in a lambda's body on any
element as the row's. Polars runs them; for DuckDB, see "Lists run on
DuckDB". This also fixes the Ibis producer reading `t.select(a=t.s.a)`
as the table's first column.

### A batch updates a source table at the cost of the change

Applying a batch to a pipeline's copy of a source table no longer groups the
whole table. A batch of inserts appends them, and deletes touch only the rows
equal to a deleted row. On the metrics benchmark (2.4 million rows, one minute
of samples per refresh) this was about 200 ms of a 365 ms refresh.

### A stale checker fails with a clear message

`substrait-check --version` prints the checker's protocol, and sverify checks
it once per process: a checker older or newer than the package raises
`sverify.errors.CheckerVersionError`, which says how to rebuild it (`uv sync`
or `lake build substrait-check`), where a stale build used to fail later with a
`KeyError`.

### `inf - inf` and `0 * inf` are NaN under `semantics="duckdb"`

With DuckDB's semantics, `+`, `-` and `*` of doubles now lift to what DuckDB
computes: NaN for `inf - inf`, `-inf + inf` and `0 * inf`, as `/` already
gave for `inf / inf` and `0 / 0`. Lean's generated lift table states them
exactly (`DuckFn.addDouble`, `subDouble`, `mulDouble`), so the plan Lean writes
back runs on DuckDB and gives NaN too, where it used to raise "domain error".
The reference semantics still raises there (#257).

### Engine facts: JSON only, and an `io` layer

The facts in `characterization/<engine>/facts/` are the record: the generated
`FACTS.md` overviews, `python -m sverify_dev.facts --write` and their step in
the `Generated files` workflow are gone; `python -m sverify_dev.facts` checks the
documents. `fact.schema.json` has a layer and an area `io` (how an engine reaches
data: extensions, catalogs, object stores, credentials) and a status
`workaround`. The first: DuckDB's `unity_catalog` extension's ATTACH ignores a
named secret unless it names it (`duckdb-IO1`) and ignores the vended `endpoint_url`, so a
MinIO behind Unity Catalog needs DuckDB's `s3_endpoint` settings (`duckdb-IO2`);
its `delta` reader is then denied with the table-scoped keys (`duckdb-IO3`, open).

### A fast default test suite

`poe test` runs the fast Python tests on 2 workers: it leaves out the tests
marked `slow` (engine agreement on many queries, long streams, replays, and the
Spark tests) and runs a tenth of each Hypothesis test's examples (the `dev`
profile, `SVERIFY_PROFILE`). `poe test-all` and `poe qa` run every test with
the full counts, as CI does; CI splits the `core` tests into three shards
(`SVERIFY_SHARD`, `python/tests/conftest.py`).

### Nightly wheels

Each night, when `main` has changed, the Wheels workflow builds and tests the
wheels for every platform and publishes them as the rolling
[`nightly` pre-release](https://github.com/AlexanderNenninger/substrait-lean/releases/tag/nightly),
versioned `<next minor>.dev<commits>+g<sha>`. Install them with
`uv add "sverify>=0.4.0.dev0" --find-links https://github.com/AlexanderNenninger/substrait-lean/releases/expanded_assets/nightly`
or `pip install --pre sverify --find-links …`; `python/README.md` has the
details. Each build's wheels stay on the release for 30 days, so a pinned wheel
URL works that long. They never go to PyPI.

### No more Intel macOS wheels

Wheels exist for Linux (x86_64, aarch64) and macOS on Apple silicon (arm64).
On an Intel Mac, pip and uv build `sverify` from the sdist, which needs
[elan](https://github.com/leanprover/elan).

### The tour is five notebooks

The tour has three workflows (duplicate payments, sensor alerts, an orders
mart) and two guides: contracts (chapters 4 to 8 merged) and pipelines and
engines (chapters 9 to 12 merged). The start page and the chapters on how it
works moved to `docs/how-it-works.md`. Chapter 17 is now
`catalogue/backend_semantics.py`.

### Windows over time frames recompute only the rows near the change (tested)

A node of window aggregates over bounded RANGE frames of one time column
(`range=(-ibis.interval(minutes=5), 0)`) recomputes only the output rows
whose frames a batch's rows fall in, from the input rows those frames read.
This strategy is tested, not proved: `status()` and the refresh summary say
"touched frames recomputed (tested, not proved)", and the lemma it rests on
is #458 (#294).

### Touched groups read only the touched time range

When one of an aggregate's group keys is a fixed-width time bucket
(`ts.truncate("m")`, `ts.bucket(...)`), recomputing the touched groups reads
the input through the range those buckets cover, so the engine skips the
other rows while it scans. The semi-join on the keys still picks the exact
rows, and a touched NULL bucket reads the whole input.

### Aggregates recompute only the groups a batch touches

A node that ends in a `GROUP BY` over an input with delta rules no longer
recomputes and diffs its whole result on every refresh. It takes the group
keys of the input rows the batch inserts or deletes, recomputes those groups
(a semi-join on the keys) and replaces their rows, for any measure: MIN, MAX,
AVG, COUNT, SUM and the rest. Lean proves the split
(`TouchedGroups.touched_sound`). `status()` and the refresh summary say which
strategy ran. Other nodes without delta rules are still recomputed and
diffed, and #248 stays the issue for delta rules of aggregates.

### Windows recompute only the partitions a batch touches

A node whose window functions share one `PARTITION BY` (with the partition
keys among its columns) recomputes only the partitions a batch touches, the
way an aggregate recomputes its touched groups. Lean proves it from
`windowEval_sharded` (`TouchedGroups.touched_window_sound`), for inputs
without ties on the partition and sort columns. Windows with different
partitions, or none, are still recomputed and diffed.

### `division_type: TRUNCATE` is accepted

A plan whose `modulus` states `division_type: TRUNCATE` was refused,
although the remainder already takes the dividend's sign. It is now
accepted; `FLOOR` is still refused, as the model does not compute it.

### `approx_nunique` is refused

Ibis's `approx_nunique()` was translated as the exact `nunique()`. Each
engine computes its own estimate, so no plan gives the same answer
everywhere; it is now refused, with a hint to use `nunique()` for the exact
count.

### Isthmus support removed

sverify no longer compiles SQL strings with Isthmus (substrait-java's
Calcite-based compiler). Its frontends are Ibis and SQL through sverify's
own producers (#211, #231). `sverify.engines.isthmus_json`,
`sverify.engines.SQL_PRODUCERS`, `sv.connect(sql_producer=...)` and the
`SVERIFY_ISTHMUS` variable are gone. SQL strings need the `datafusion` extra
until the SQLGlot frontend replaces DataFusion's producer.

### Maintainer tooling leaves the wheel

The coverage harness, the query catalogue, the fuzzers, DuckDB's
sqllogictest replay and the example pipelines (`sverify.coverage`,
`sverify.catalogue`, `sverify.fuzz`, `sverify.duckdb_fuzz`, `sverify.slt`,
`sverify.examples`) were internal, and only the tests and CI used them. They
now live in `python/tools/sverify_dev` in the repository and are no longer
installed with sverify: about 4,000 lines fewer in the wheel.

### Fixed: a sink kept another plan's rows after the plan changed

If you use 0.3.0 and change a node's transform while keeping its sink,
upgrade. The sink recorded which plan wrote each state, but only compared
the state's epoch (the sum of the source versions) when deciding what to
write. So a job restarted with a new plan, at source versions the sink had
already committed, skipped the write: the table kept the old plan's rows and
its contract, while the node held the new plan's state. On the next source
change it merged the new plan's change on top of the old plan's rows, and
the table was wrong from then on, without an error. This affected
`DeltaSink`, `IcebergSink`, `sink_from` and sinks of your own that override
`committed()`.

A sink whose last commit came from another plan (`Contract.plan` differs) is
now overwritten with the new plan's whole state, and the refresh reports the
write as `overwrite`. `DeltaSink` replaces the table's schema and drops the
CHECK constraints it added for the old plan that the new one does not prove,
then adds the new plan's in the commit that records the epoch, so a job
stopped in between writes the state again. `IcebergSink` replaces the
table's schema in the overwrite's transaction. Constraints that another
writer added still stop the write.

A table is affected if you restarted a job with a changed plan before its
sources moved on. If it has not written a change since, the first refresh
after upgrading overwrites the table. If it has, that MERGE recorded the new
plan, and the fix cannot tell the table is wrong: delete the table, or point
the sink at a new location, and refresh to write it in full.

### Fixed: a node without a contract is planned again after a schema change

A node of a plain function, such as `orders.pipe(lambda t: t.select(t.id))`,
counted as contracted, so a dropped column, or a column widened beyond what
its values used to fit, raised `SchemaError` instead of planning the node
again. It is now planned again and recomputed, and its sink is overwritten.

### Changed: no operation creates a NaN

A NaN in your data still passes through, but an operation on numbers no
longer makes one where IEEE would. `inf - inf`, `0 * inf`, `inf / inf`,
`fmod(inf, y)`, a negative number to a fractional power, `sin`, `cos` or
`tan` of an infinity, and a grouped double `SUM` or `AVG` of both `+inf` and
`-inf` now raise a domain error on DuckDB, Polars, Spark and Snowflake, and
`verify` reports "domain error" unless the plan rules it out. So a job with
no NaN in its inputs has none in its outputs. For double arithmetic on
columns `verify` cannot bound, add bounds such as `_.x < 1e300` and
`_.x > -1e300` to `requires`. Adding a constant, or a whole-number power,
needs none. A plan that asks for `on_domain_error: NAN` is refused, and
`on_division_by_zero: IEEE` still gives NaN for `0.0 / 0.0`, as it asks.
DataFusion still gives NaN where the others raise (#257).

### Fixed: `%` of doubles gave wrong values

A plan that takes the remainder of doubles, such as `x % 2.5`, passed the
check but was evaluated on the doubles' internal codes, so its values were
wrong (`7.5 % 2.0` came out as a 300-digit integer). It is now C's `fmod`,
as DuckDB, DataFusion and Spark compute `%`: the result has the sign of the
dividend (`-7.5 % 2.0` is `-1.5`), a NaN gives NaN, an infinite dividend
raises (see above), and an infinite divisor gives the dividend. The value is exact. A zero
divisor is an error, as for integers, so `verify` reports "division by zero"
unless the plan rules it out (`WHERE y <> 0.0`). The Polars translation gives
the same results, although Polars' own `%` takes the divisor's sign.
Substrait itself defines no `modulus` of doubles (#203).

Substrait defines no `modulus` of doubles, so plans now call sverify's own
`sverify_fmod` for it, which the Ibis producer and the SQL lift emit for `%`
of doubles and which DataFusion runs as its own `%`. sverify still reads the
`modulus` of doubles that DataFusion's producer writes (#256).

## 0.3.0 (2026-11-01)

### Licensed under the MPL-2.0

sverify now has a license, the Mozilla Public License 2.0; 0.2.0 and earlier
were published without one. You can use sverify in open and proprietary
products alike. If you distribute changes to sverify's own files, they stay
under the MPL. The vendored `ibis_substrait` stays under Apache-2.0.

### Nodes compose left to right with `.pipe`

A job now reads in the order its data flows
([#189](https://github.com/AlexanderNenninger/substrait-lean/issues/189)).
It adds to the API and changes nothing that exists.

```python
paid_orders = orders.pipe(paid).write(DeltaSink("lake/paid"))     # chain, then store
enriched = paid_orders.pipe(enrich, customers=customers)          # fan-in by keyword
regional = paid_orders.pipe(
    sv.sql("SELECT o.*, c.region FROM orders o JOIN customers c ON c.cid = o.cid"),
    customers=customers,
)                                                                 # SQL is a step
quick = orders.pipe(lambda t: t.filter(_.amount > 0))             # no contract
sv.group(paid_orders.pipe(daily_totals), enriched).refresh()      # fan-out
```

- `Node.pipe(step, /, **inputs)`, and `pipe` on every source in
  `sverify.io`, apply a step to the node: the chained node fills the step's
  first table parameter, and the other inputs come by keyword. It builds the
  same node and plan as the call form `paid(orders)`, which stays public.
  A missing, duplicate or unknown input raises `TypeError` naming the step's
  parameters.
- A step is a contracted transform, a plain function from Ibis tables to an
  Ibis table (a transform with no contract), or `sv.sql(query)`.
- `sv.sql(query, *, as_=None)` without tables is a step whose inputs are the
  tables the query reads (not its CTEs, and each once). The keyword inputs
  bind their own names, and the chained node binds to the one table left
  over. A table with no input, an unused chained node, a keyword the query
  doesn't read, or an `as_` that isn't the table left over raises
  `TypeError`. `sv.sql(query, orders=orders)` inside a transform is
  unchanged.
- The README, the tour and the API reference lead with `.pipe`.

### Your own sources and sinks

Writing a source or a sink no longer means knowing sverify's internals
([#156](https://github.com/AlexanderNenninger/substrait-lean/issues/156)).

- `sverify.io.Source`: implement `read(since)`, which returns new rows and a
  cursor as a `Batch` (`kind="append"`, `"snapshot"` or `"changes"`).
  sverify numbers the reads as versions, keeps the table, and hands nodes
  the exact change. The refresh report says what the batches assume, and
  `refresh(audit=True)` reads the table again in full to check it, also
  when no batch arrived. `from_query(fn, cursor_on=...)`, `from_frame(fn)`
  and `from_files(path)` build one.
- `sverify.io.Sink`: implement `write(change)`, which gets a `SinkChange`
  (rows added and removed, or the whole table, and the contract), and
  optionally `committed()`. Exactly-once skipping and contract recording
  happen once, in the base class. `sink_from(fn)` hands the whole table to
  a function. Nodes reading a stored node of your own sink read what was
  written, with its exact changes. `DeltaSink` and `IcebergSink` are now
  subclasses, and every sink reports a `SinkWrite` (new mode `"update"`;
  `version` may be None).
- The full protocol for table formats is public as
  `sverify.io.VersionedSource`, with `Snapshot` and `SourceBatch`, whose
  `unchanged`, `from_changes` and `from_snapshot` build what `changes`
  returns. `Pipeline` no longer special-cases `StaticSource`: any source
  with a `digest` gets it recorded.
- `sverify.io.Storage` holds object store options shared by several tables:
  a mapping, or a function returning fresh options whenever a table is
  opened, so expiring tokens renew; `repr` shows option names only.
  `DeltaSource` and `DeltaSink` take one, or a function, as
  `storage_options`.
- A sink's `app_id` now defaults to `sverify:<sink name>` (it was the
  node's name, which is the same unless it clashed with a source's).
- `Contract.from_json` ignores fields it does not know, so contracts can
  gain fields without breaking the readers of this version.

### A pytest plugin for transforms and contracts

`sverify.testing` is now public
([#180](https://github.com/AlexanderNenninger/substrait-lean/issues/180)), and
installing sverify registers a pytest plugin (the `pytest11` entry point
`sverify`, off with `-p no:sverify`).

- `assert_contract(node)` asserts that every contract in a node's lineage is
  proved. With `data=` it runs the node on those rows: test data that breaks
  a precondition is reported with its rows, the output is checked against
  the postconditions, and with `expected=` it is diffed against the expected
  rows (missing and unexpected rows, as bags).
- `assert_engines_agree(node, data)` runs the node on every installed engine
  and diffs their results.
- `cases(node, max_rows=5)` is a Hypothesis strategy of input tables that
  meet a node's preconditions, for property tests of the code around it.
  It needs the new `testing` extra (`pip install 'sverify[testing]'`).
- The fixtures `sv_source(rows, schema, name=...)` (an in-memory source,
  also `sverify.testing.source`) and `sv_engine`, which runs a test once per
  installed engine (`installed_engines()`), or per engine of
  `--sv-engines=duckdb,polars`.

`python/tests/test_plugin_example.py` is an example test file, and
`python/tests/test_tour.py` tests the tour's transforms with the plugin.

### Ibis string functions

More of Ibis's string API is checked and runs on every engine
([#49](https://github.com/AlexanderNenninger/substrait-lean/issues/49)):
`lpad`/`rpad`, `repeat`, `reverse`, `replace`, `ilike`, `ascii`,
`levenshtein`, `right`, `find` with a start, `join` (`concat_ws`),
`find_in_set`, `capitalize` and slices. Each has the meaning of Ibis's
DataFusion SQL, by code point. A `repeat` past 2³¹ − 1 bytes is an
`overflow` error, which the checker rules out for a constant string with a
bounded count.

- Polars computes all of them exactly. DuckDB, Snowflake and Spark raise
  "non-ASCII text differs between engines" for `reverse`, `ascii`,
  `levenshtein` and `ilike` on non-ASCII text, and refuse `replace` with an
  empty pattern.
- `translate` is refused: DataFusion translates grapheme clusters.

### Fixes

- Written plans keep a projected literal's declared type: doubles,
  timestamps and typed NULLs no longer come out integer-typed
  ([#96](https://github.com/AlexanderNenninger/substrait-lean/issues/96)).
- The tour notebooks declare the extras they use (`sverify[datafusion]`,
  `sverify[datafusion,polars]`), so they run in their own sandbox, as molab
  runs them
  ([#197](https://github.com/AlexanderNenninger/substrait-lean/issues/197)).

## 0.2.0 (2026-11-01)

A new public API, built around transforms that compose
([#164](https://github.com/AlexanderNenninger/substrait-lean/issues/164)).
It is a clean break: the old names are gone, with no deprecated aliases. The
proofs, the Lean model and what each engine computes are unchanged.

### Transforms compose; there is no pipeline object

```python
import sverify as sv
from sverify.io import DeltaSink, DeltaSource

orders = DeltaSource("s3://lake/orders")
p = paid(orders).write(DeltaSink("s3://lake/paid"))      # stored, and a source downstream
r = revenue(p).write(DeltaSink("s3://lake/revenue"))

r.refresh()                    # DuckDB in memory by default
r.refresh(engine="polars")     # or "datafusion", "spark", a Spark session
r.to_arrow(); r.to_polars(); r.to_pandas(); r.table
```

- A contracted transform (`@sv.transform`) called on a source or a node
  builds a `Node`. The contract is checked when the node is built: a link
  whose upstream guarantees don't imply the downstream assumptions raises
  `CompositionError` at once. Called on Ibis tables, a transform still
  returns an Ibis expression.
- Without a `.write` between transforms, they fuse into one plan and one
  incremental view, and the intermediate rows are never stored.
- `.write(sink)` stores a node, in the middle of a job or at its end, exactly
  once per state. It returns a node that downstream transforms read as a
  versioned source (Delta's Change Data Feed, Iceberg's snapshots), building
  on the contract its own stage proved.
- `refresh()` on any node brings its whole lineage up to date, upstream
  first, refreshing every node once per call and writing every stored node
  once. A restarted job rebuilds the same nodes; the first refresh resumes
  each stored node from its table.
- The engine is chosen at refresh time, not when the job is built.
  `"spark"` and Spark sessions are new as engines for maintained results.
- `sv.group(a, b).refresh()` refreshes several outputs against the same
  source versions and shares the stored nodes they read; `.status()` reports
  on each.
- `node.plan` is the plan Lean checked, for `sverify.engines`.

### SQL models

A transform's body can be SQL over its inputs, by keyword name:

```python
@sv.transform(requires={"orders": ["amount_cents >= 0"]}, ensures=["revenue_cents >= 0"])
def revenue(orders):
    return sv.sql("""
        SELECT region, coalesce(sum(amount_cents), 0) AS revenue_cents
        FROM orders GROUP BY region
    """, orders=orders)
```

`sv.sql(query, **tables)` returns an Ibis table, so a SQL model is an
ordinary node. It fuses with its neighbours, can be stored with `.write`,
composes with Ibis transforms on either side and reads several inputs. Its
schema and plan come from DataFusion's SQL producer, or Isthmus's without
DataFusion, and work on the placeholder tables nodes are built from. A query
the producer can't plan, or a plan Lean refuses, raises `Unsupported` saying
which part; without either producer the error names the `datafusion` extra.

### A small namespace

`import sverify as sv` holds eleven names: `transform`, `sql`, `verify`,
`unique`, `references`, `Report`, `Changes`, `group`, `connect`, `asof_join`
and `Node`. Three submodules hold the rest:

- `sverify.io`: `DeltaSource`, `DeltaSink`, `IcebergSource`, `IcebergSink`,
  `SinkWrite`, `Contract`, `StaticSource`.
- `sverify.engines`: running plans, SQL dialects and plan tools.
- `sverify.errors`: the exceptions.

Every other module (`sverify.incremental`, `sverify.contracts`,
`sverify.engine`, `sverify.sql`, `sverify.partition`, the per-engine modules,
`sverify.ibis_substrait`, `sverify.catalogue`, `sverify.coverage`,
`sverify.fuzz`, `sverify.testing`, `sverify.counterexample`,
`sverify.display`, `sverify.examples`, `sverify.io.delta`,
`sverify.io.iceberg`) is internal and may change in any release.

### Other changes

- Sinks no longer take a view: `DeltaSink(uri)`, `IcebergSink(catalog,
  identifier)`, attached by `node.write(sink)`. There is no public
  `sink.write()`: refresh writes. Delta and Iceberg sinks report through one
  type, `SinkWrite` (it replaces `IcebergWrite`).
- Sources and sinks take `name=`, the table's name in the plans that read
  them. It defaults to the last part of the URI or identifier.
- `StaticSource.apply(sv.Changes(...))` changes some rows of an in-memory
  source; the next refresh gets exactly that change, where `replace` makes
  it diff the whole table. `StaticSource` takes `name=`.
- A node without delta rules (left join, aggregate, window, `DISTINCT`,
  `LIMIT`) is recomputed and diffed, as views were inside a `Pipeline`. The
  standalone `IncrementalView`'s refusal (`NotIncremental`) is no longer on
  the public path.
- Incremental views over SQL strings become transforms whose body is
  `sv.sql(...)`.
### Fixes

- Arithmetic on double literals (`3.0 / 2.0`, a `CASE` of double literals
  plus `1.0`) used the integer operators on the literals' codes, which gave
  false proofs; the parser now reads a double literal, a cast to a double or
  such a `CASE` as a double
  ([#97](https://github.com/AlexanderNenninger/substrait-lean/issues/97),
  [#155](https://github.com/AlexanderNenninger/substrait-lean/pull/155)).
- Booleans are ordered FALSE < TRUE, as DataFusion orders them; `b < TRUE`
  was NULL in the model
  ([#154](https://github.com/AlexanderNenninger/substrait-lean/issues/154),
  [#155](https://github.com/AlexanderNenninger/substrait-lean/pull/155)).
- A bare double literal (`SELECT 1.5 AS c`) is written as an `fp64` literal,
  not as an integer holding its code, and `substrait-check` prints such a
  column as doubles. `0.0` and `CAST(NULL AS DOUBLE)` still come out with an
  integer column type (part of
  [#96](https://github.com/AlexanderNenninger/substrait-lean/issues/96),
  [#166](https://github.com/AlexanderNenninger/substrait-lean/pull/166)).
- A `DeltaSink` refused its second write when a guarantee had parentheses
  that Delta drops when it stores a CHECK constraint
  (`(x IS NULL) OR (x > 0)`).

### Moved

| 0.1 | 0.2 |
|---|---|
| `sv.Pipeline`, `pipe.source`, `pipe.view`, `pipe.refresh` | transforms on sources, `node.write(sink)`, `node.refresh()`, `sv.group(...)` (`Pipeline` is internal: `sverify.incremental`) |
| `sv.IncrementalView(con, query, name)`, `view.apply`, `view.rows()` | a transform on a `StaticSource`, `source.apply(sv.Changes(...))`, `node.refresh()`, `node.to_arrow()` (`IncrementalView` is internal) |
| `pipe.view(..., resume=source.stored())` | build the nodes again; the first refresh resumes |
| `DeltaSink(uri, view).write()` | `node.write(DeltaSink(uri))`, written by `refresh` |
| `IcebergSink(catalog, identifier, view).write()` | `node.write(IcebergSink(catalog, identifier))` |
| `sverify.io.SinkWrite`, `sverify.io.IcebergWrite` | `sverify.io.SinkWrite` |
| `sv.StaticSource` | `sverify.io.StaticSource` |
| `sv.Changes` | `sv.Changes` (unchanged) |
| `sv.connect`, `sv.transform`, `sv.verify`, `sv.unique`, `sv.references`, `sv.Report`, `sv.asof_join` | unchanged |
| `sv.run_plan` | `sverify.engines.run` |
| `sv.run_substrait_json` | `sverify.engines.run_substrait_json` |
| `sv.create_table` | `sverify.engines.create_table` |
| `sv.table_rows` | `sverify.engines.table_rows` |
| `sv.ENGINES` | `sverify.engines.ENGINES` |
| `sv.SQL_PRODUCERS` | `sverify.engines.SQL_PRODUCERS` |
| `sv.Connection` | `sverify.engines.Connection` |
| `sv.substrait_json` | `sverify.engines.substrait_json` |
| `sv.isthmus_json` | `sverify.engines.isthmus_json` |
| `sv.written_plan` | `sverify.engines.written_plan` |
| `sv.delta_plans` | `sverify.engines.delta_plans` |
| `sverify.sql.to_sql`, `Dialect`, `Unsupported` | `sverify.engines.to_sql`, `Dialect`, `Unsupported` |
| `sverify.sql.duckdb.DUCKDB`, `sverify.sql.snowflake.SNOWFLAKE`, `sverify.sql.spark.SPARK` | `sverify.engines.DUCKDB`, `SNOWFLAKE`, `SPARK` |
| `sverify.partition.run_sharded` | `sverify.engines.run_sharded` |
| `sverify.spark_engine.run` | `sverify.engines.run_spark` |
| `sverify.spark_engine.SPARK_CONF` | `sverify.engines.SPARK_CONF` |
| `sv.VerificationError` | `sverify.errors.VerificationError` |
| `sv.PreconditionError` | `sverify.errors.PreconditionError` |
| `sv.PostconditionError` | `sverify.errors.PostconditionError` |
| `sv.CompositionError` | `sverify.errors.CompositionError` |
| `sv.NotIncremental` | `sverify.errors.NotIncremental` |
| `sv.SqlError` | `sverify.errors.SqlError` |
| `sverify.incremental.SchemaError` | `sverify.errors.SchemaError` |
| `sverify.incremental.AuditError` | `sverify.errors.AuditError` |
| `sv.Issue`, `sv.References`, `sv.Unique` | internal (`sverify.contracts`); `sv.unique` and `sv.references` build them |
| `sverify.io.ColumnStats`, `sverify.io.stats_facts`, `sverify.io.Stored` | internal (`sverify.io._common`, `sverify.incremental`) |

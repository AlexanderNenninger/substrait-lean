# Release notes for 1.0.0rc1 (draft)

A draft of the notes for the first release candidate of 1.0 (#756), for
someone upgrading from 0.8.0. The maintainer decides when rc1 is tagged.
Until then this page follows `changelog.d/`, which holds one fragment per
change; at the release the fragments go into `CHANGELOG.md` in full
(`.claude/skills/release-sverify/SKILL.md`). This page collects what an
upgrade has to change and the defaults that changed under it.

Sverify 1.0 keeps no deprecated alias. A renamed or removed name raises
`AttributeError`, `TypeError` or `ImportError`, and the formats Sverify
reads back read their earlier versions too ([stability.md](stability.md)).

## Install

- `pip install sverify` installs no engine. Add the engine you run:
  `sverify[duckdb]`, `sverify[polars]`, `sverify[spark]`, or `sverify[all]`.
  `sv.verify`, the SQL dialects and `report.to_sql` work without one
  (`changelog.d/1485-duckdb-is-an-extra.md`).
- Each engine package covers the minor release its facts were probed at:
  `duckdb>=2.0.0,<2.1`, `polars>=2.1.0,<2.2`, `pyspark>=4.3.0,<4.4`. A run on
  another patch of that minor warns (`EngineVersionWarning`); a run on
  another minor raises `EngineVersionError`
  (`changelog.d/2052-engine-version-ranges.md`).
- Python 3.12 or later.
- `sverify-dbt` is released at the same version and pins `sverify==<version>`.

## Command line

The exit codes run from the best to the worst, so the worst of several runs
is their maximum. `sverify.cli.ExitCode` names them
(`changelog.d/2458-exit-severity.md`):

| Outcome | 0.8.0 | 1.0 |
|---|---|---|
| proved | 0 | 0 |
| not proved | 1 | 1 |
| usage | 2 | 2 |
| unsupported | 3 | 3 |
| refused: no route to the engine | new | 4 |
| budget exceeded | 4 | 5 |
| quarantined | 5 | 6 |
| held | new | 7 |
| error | 6 | 8 |

- `--json` and `--output-format` are removed: write `--format json`, or
  `--format X` (`changelog.d/2345-one-name-per-concept.md`,
  `changelog.d/881-drop-output-format.md`).
- `sverify contract export` drops `--format odcs`
  (`changelog.d/2081-contract-export-format.md`).
- `check --require-proved` exits 1 for a node whose postconditions are only
  checked on the data (`changelog.d/881-cli-exit-codes-require-proved.md`).
- `sverify check query.sql --schema schemas.yaml` checks a bare SQL file
  (`changelog.d/1362-check-sql-file.md`).

## Python names

Old → new, with no alias. `changelog.d/2345-one-name-per-concept.md` has the
complete list, and `changelog.d/2081-remove-deprecated-aliases.md` and
`changelog.d/886-remove-deprecated-api.md` the removals.

| 0.8.0 | 1.0 |
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
expect (`changelog.d/1484-report-verdict.md`). `SinkChange` takes keywords
(`changelog.d/2343-batch-refresh-sink-change.md`), and
`RefreshReport.diffed` is a dict of node to reason
(`changelog.d/742-node-mode.md`).

## Defaults that changed

- Checks on data run the proved plan on the engine of the table's
  connection, where they went through Ibis. A condition outside the model
  now raises `UnsupportedError`. Sverify's own DuckDB connections, those of
  `sv.connect()` among them, run at the time zone UTC
  (`changelog.d/2342-checks-run-the-proved-plan.md`).
- `Report.run` runs the rewritten plan where one of seven proved rewrites
  applies and the preconditions were checked on the data;
  `run(optimize=False)` keeps the plan as written
  (`changelog.d/1787-rules-on.md`).
- The default observation reads `-0.0` and `0.0` as one value, every NaN as
  one, and a list's elements as a multiset; `elements="sequence"` observes
  their order (`changelog.d/1285-default-observation.md`).
- `Report.run` compares each table it reads with the schema the plan was
  verified for, and refuses a mismatch before a row is read
  (`changelog.d/1540-run-checks-the-schema.md`).
- Under `semantics="reference"`, DuckDB SQL's `CAST(x AS <integer>)` of a
  double or a decimal is refused, since DuckDB rounds where the reference
  truncated: write `CAST(round(x) AS BIGINT)`, `floor` or `ceil`
  (`changelog.d/1484-dialect-differences.md`).
- A Polars or Spark run no longer runs the plan on DuckDB first, and
  `requires` are checked on the run's own engine
  (`changelog.d/1484-assumed-on-the-run-engine.md`,
  `changelog.d/1484-requires-on-the-engine.md`).

## Formats

Each changed format is bumped once. Sverify reads the earlier versions of
the formats it reads back ([stability.md, The formats](stability.md#the-formats)).

| Format | 0.8.0 | 1.0 | What changed |
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

## sverify-dbt

- `sverify-dbt check --format json` prints the envelope of
  `sverify check --format json`; its models are `items`
  (`changelog.d/891-dbt-json-envelope.md`).
- It exits as `sverify check` does, and its `--fail-on` levels nest:
  `contract`, `unproved`, `refused` (`changelog.d/891-dbt-exit-codes.md`).
- Statuses are snake_case (`"not_proved"`, `"not_checked"`),
  `sverify_dbt.Needed` is `NeededTest`, and `CheckResult.proved` is
  `proved_tests` (`changelog.d/891-dbt-result-names.md`,
  `changelog.d/1484-report-verdict.md`).

## Before tagging

- The fragments since 0.8.0 are the source. Fold them into `CHANGELOG.md`
  at the version bump, and check this page against them once more.
- Some changes merged without a fragment. Where users notice one, add it
  first.

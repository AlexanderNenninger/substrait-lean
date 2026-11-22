### One name for each concept in the public API (breaking)

The 1.0 naming sweep ([#2345](https://github.com/AlexanderNenninger/substrait-lean/issues/2345), ruling 263) gives each concept one name across the Python API, the formats and the command line. No old name stays as an alias: each raises `AttributeError`, `TypeError` or `ImportError`, or is a key a reader of the new format maps. A `reason` is a code and `why` is words, in the Python API and the JSON sverify writes per run; a stored table's columns and record keys keep their names, so the quarantine table's `_reason` and its record's `reason` stay (`docs/stability.md`, ruling 264).

Python names, old → new:

- `sverify.types.Observation` → `sverify.types.Lenses`, as `Report.lenses` names it.
- `sverify.types.CheckedCondition` (the items of `Report.ensures`) → `sverify.types.Postcondition`: "check" reads data (F219).
- `sverify.errors.SqlError` → `SQLError`, cased as `SQLStep`.
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
- The command line's JSON is format 2, and the refresh report's JSON (`Refresh.to_json`) is format 2. A write's `inserted` and `deleted` are `inserts` and `deletes`, and in the command line's JSON a fix's `reason` (`check --fix`, `--diff`) is `why`. The refresh report's `$schema` is `…/schemas/refresh/2.json`. Jobs that read these documents read the new keys.

Command line: `--json` is removed. Write `--format json`. `sverify-dbt check --format json` writes format 2 of the same document.

Messages follow the names. A refresh that finds the stored state verified under other semantics says "the plan was verified under semantics='duckdb', and is now under semantics='portable'", and `sverify check --against-sink` says "(semantics='portable' then, 'duckdb' now)". A retention line names the node.

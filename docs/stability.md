# Stability in 1.x

A pipeline that runs sverify 1.0 keeps running on every 1.x release. Sverify
keeps three promises to it:
the formats a running pipeline reads don't break, a contract proved in 1.x
stays proved, and a break of the Python API is loud and comes with a
migration note. This page states each rule and the test that holds sverify
to it.

## The formats

Jobs and tools read these formats that sverify writes:

| Format | Where it lives | Version | Schema |
|---|---|---|---|
| The sink's contract record | the key `sverify.contract` in a Delta commit's `commitInfo` and in an Iceberg table's properties, and the snapshot summary keys `sverify.plan`, `sverify.epoch` and `sverify.app`; wherever a `Sink` of your own stores `Contract.to_json()` | `format` 2 in the record | [`sink-contract.schema.json`](../python/src/sverify/schemas/sink-contract.schema.json) |
| The Substrait contract metadata | the message `io.sverify.substrait.v1.Contract` in an exported plan's `advanced_extensions`, from `Report.to_substrait`, and `Report.substrait_contract()` | `format` 2 in the manifest | [`substrait_contract.proto`](../python/src/sverify/substrait_contract.proto) and [`substrait-manifest.schema.json`](../python/src/sverify/schemas/substrait-manifest.schema.json) |
| The report's JSON | `Report.to_json()`, read back by `Report.from_json()` | `format` 2 in the document | [`report.schema.json`](../python/src/sverify/schemas/report.schema.json) |
| The command line's JSON | what `sverify check`, `refresh` and `explain` print with `--format json`, with each node's report as `Report.to_json()` writes it; the exit codes are part of it | `format` 1 in the document | [`cli.schema.json`](../python/src/sverify/schemas/cli.schema.json) |
| The quarantine table | a Delta or Iceberg table next to a node's sink; each write's record in a Delta commit's `commitInfo`, or an Iceberg snapshot's summary, under the key `sverify.quarantine` | `format` 1 in the record | [`quarantine.schema.json`](../python/src/sverify/schemas/quarantine.schema.json) |
| The refresh report's JSON | `Refresh.to_json()` | `format` 1 in the document | [`refresh.schema.json`](../python/src/sverify/schemas/refresh.schema.json) |

Within 1.x each format follows these rules:

- A format only gains optional keys or fields. A key keeps its name, its
  type and its meaning, and stays as long as 1.x lasts.
- A reader ignores keys it does not know. A job on an older 1.x release
  reads what a newer one wrote, and sees what it knows of it.
- Every 1.x release reads what every earlier 1.x release wrote, and the
  records of the releases before 1.0 that the fixtures hold, from 0.4.0 on.
- Each format keeps the version the table gives throughout 1.x: 2 for
  the sink's contract record, the Substrait metadata and the report's JSON,
  which 1.0 renamed,
  and 1 for the command line's JSON, the quarantine record and the refresh
  report, which have had one shape since they were added. A reader refuses a
  format newer than it knows, with an error that says to upgrade sverify.
- A value from a fixed set, such as the manifest's `class` or a condition's
  `kind`, may gain new values. A reader that meets one it does not know
  says so in its error.

For the first three, format 1 is the shape before 1.0, and 1.0 renamed its keys so that each
concept has one name: `semantics`, `equivalence` and `node`. A reader maps a
sink's record or a manifest of format 1:

- the sink's record names the node `view`, and Delta keeps it under the
  key `sverify`; a record written before 0.5 has no `format`;
- the manifest says `profile`, `observation` and `observation_components`
  for `semantics`, `equivalence` and `equivalence_components`.

The report's JSON of format 1 was in no release, and `Report.from_json`
refuses it. In format 2 its postconditions, issues and assumptions take the
shape of a SARIF 2.1.0 result, so that `sverify check --format sarif` only
wraps them in a run:
`ruleId`, the code in snake_case (`may_be_false`, `division_by_zero`);
`level`, SARIF's `error`, `warning`, `note` or `none`; `kind`, `pass` or
`fail`; `message.text`; and sverify's own fields under `properties`.

Each release writes fixtures of the formats it writes into
[`python/tests/formats/<version>/`](../python/tests/formats/), with
`python -m sverify_dev.formats`. [`tests/test_formats.py`](../python/tests/test_formats.py)
reads every fixture, checks it against its schema, and reads it with the
API a job uses: a sink resumes from the Delta table and reads its contract,
`sv.Report.from_substrait` reads each export and proves its contract again, and
`Report.from_json` reads each report back to the same document.
The fixtures of 0.4.0 were written by the release on PyPI.

### The Substrait contract message

The protobuf message follows
[protobuf's rules for updating a message](https://protobuf.dev/programming-guides/proto3/#updating),
which keep old readers and old data working:

- The package `io.sverify.substrait.v1` and the type URL
  `type.googleapis.com/io.sverify.substrait.v1.Contract` stay. A message that
  breaks these rules goes in a new package, `v2`, in sverify 2.0.
- A field keeps its number and its type. A new field takes a new number. A
  field no longer written is marked `reserved`, by number and name, so that
  neither is used again.
- The manifest, a `google.protobuf.Struct`, follows the rules of the JSON
  formats above. Its keys are in
  [the guide](tasks.md#exporting-to-substrait).
- `sv.Report.from_substrait` reads every earlier 1.x export and proves its contract
  again; for an export of a proved plan the report is proved.

The exported plan is Substrait, at the version the export names (`version`
in the plan, `substrait` in the manifest: 0.106.0 today). A minor release may
move to a newer Substrait version, and its changelog says so.

## Proofs

A contract proved in 1.x stays proved in every later 1.x release: the same
transformation, `requires`, `ensures` and `semantics` give a proved report.

The exception is a soundness fix. Where a proof turns out to rest on a
mistake, such as a Lean model of an engine that differs from the engine, a
shim that does not hold, or a misread SQL construct, the fix may refuse a
contract that was proved. Each such fix comes with:

- a changelog entry that names what is refused, why, and what to write
  instead;
- an engine fact under [`characterization/<engine>/facts/`](../characterization/)
  or an upstream record under [`upstream/bugs/`](../upstream/), with the
  evidence.

Tightening the reference semantics waits for 2.0: a change to
[the reference](reference-semantics.md) that refuses a proof the current
reference allows, such as making it raise where it returns a value. Engine
profiles follow their engine's facts, and a fact that changes a profile is a
soundness fix. The [catalogue](../catalogue/INDEX.md)'s expected results
(`catalogue/status.json`, checked by `tests/test_catalogue.py`) and the
golden tests pin what is proved, so a change to a proof shows in a pull
request's diff.

Reference changes made before 1.0, so that 1.0 starts from the tighter
reference:

- [Correctly rounded float aggregates](reference-semantics.md#of-doubles):
  a `SUM`, `AVG` or statistical aggregate of doubles is the correctly rounded
  value of the exact sum or moments. A postcondition at a rounding boundary
  can move by one ulp, which `sv.approx` absorbs.

## The Python API

The public API is what the [API reference](https://alexandernenninger.github.io/substrait-lean/)
documents. Modules and names that start with an underscore, the maintainer
tooling `sverify_dev`, and the printed text of a report (`str(report)`) are
outside it; tools read the report through its attributes or its JSON.
Two parts of `sverify.engines` are documented but outside it too, and may
change in a minor release: the plan layer (`to_sql`, `substrait_json`,
`written_plan`, `delta_plans`), which takes sverify's
internal plan, and `Dialect`'s SQL-writing methods and subclasses of it.
`Node.to_sql`, `Report.to_sql` and `Report.to_substrait` are the stable way
to a plan's SQL and Substrait.

The engines in the promise are those [Engines](#engines) lists.

A minor release may break the public API only when the break is:

- loud: a call that used the old form raises, or warns with a
  `DeprecationWarning`, and the message names the replacement;
- caught by a unit test that uses the old form;
- listed under "Breaking changes" in the changelog;
- given a migration note in that entry: what to write instead, with an
  example.

A renamed or removed name keeps working for one minor release with a
`DeprecationWarning`, and goes
in the next. A release with breaking changes lists them first in its section
of [the changelog](../CHANGELOG.md).

## Engines

This section is the one statement of which engines sverify supports; other
pages link here. The reference is Lean's reference profile
([reference semantics](reference-semantics.md)), one of the profiles that
refine the core ([core, profiles and engines](core-and-profiles.md)), and an engine runs a plan
by a route that the checker justifies against it
([routes, classes and profiles](tasks.md#routes-classes-and-profiles)).

| Engine | Runs plans | Writes its SQL | Profile (`semantics=`) | Translation from the reference | In the 1.x promise |
|---|---|---|---|---|---|
| DuckDB | `engine="duckdb"`, the default | `dialect="duckdb"` | `"duckdb"` | `Rel.duckdb_refines` | yes |
| Polars, streaming | `engine="polars"` | | `"polars"` | `Rel.polars_sound` | yes |
| Spark 4.x | `engine="spark"` | `dialect="spark"` | `"spark"` | `Rel.spark_sound` | yes |
| Snowflake | in your account, from the written SQL | `dialect="snowflake"` | none yet | | the written SQL |

`sverify.engines.ENGINES` names the engines in the promise that run plans
on a `Connection`'s tables. The engine
versions each profile describes, the class of every option on each engine
and its shims are in the [realizability table](realizability.md). The
other engines refuse the functions that only DuckDB runs so far
([`SUPPORT` and `WINDOW_SUPPORT`](../python/src/sverify/_support.py)), with a
message that points to
[the issue tracking them](https://github.com/AlexanderNenninger/substrait-lean/issues/271).
DuckDB, Polars, Spark and Snowflake are the engines of 1.0. Sverify has no
Snowflake profile or route yet: Snowflake runs the SQL sverify writes. The
`all` extra installs every engine in the promise.
Where tests compare against an engine, DuckDB is the default oracle; Lean's
model stays the reference.

## Releases

Each release is checked against these rules: the format fixtures, the "Breaking changes"
section and its migration notes, and the facts or upstream records of each
soundness fix.

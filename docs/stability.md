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
| The Substrait contract metadata | the message `io.sverify.substrait.v1.Contract` in an exported plan's `advanced_extensions`, from `Report.to_substrait`, and `Report.substrait_contract()` | `format` 3 in the manifest | [`substrait_contract.proto`](../python/src/sverify/substrait_contract.proto) and [`substrait-manifest.schema.json`](../python/src/sverify/schemas/substrait-manifest.schema.json) |
| The report's JSON | `Report.to_json()`, read back by `Report.from_json()` | `format` 4 in the document | [`report.schema.json`](../python/src/sverify/schemas/report.schema.json) |
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
  the sink's contract record, which 1.0 renamed; 3 for the Substrait
  metadata, which 1.0 renamed twice; 4 for the report's JSON, which 1.0
  renamed, gave a verdict, and then gave its lenses and facts their 1.0
  shape; and 1 for the command line's JSON, the quarantine record and the refresh
  report, which have had one shape since they were added. A reader refuses a
  format newer than it knows, with an error that says to upgrade sverify.
- A value from a fixed set, such as the manifest's `class` or a condition's
  `kind`, may gain new values. A reader that meets one it does not know
  says so in its error.

For the first three, format 1 is the shape before 1.0, and 1.0 renamed their keys so that each
concept has one name: `semantics`, `lenses` and `node`. A reader maps the
earlier formats:

- the sink's record of format 1 names the node `view`, and Delta keeps it
  under the key `sverify`; a record written before 0.5 has no `format`;
- the manifest of format 1 says `profile`, `observation` and
  `observation_components`, and of format 2 `equivalence` and
  `equivalence_components` (in an `up_to` entry too), for `semantics`,
  `lenses` and `lenses_components`;
- the report's JSON of formats 2 and 3 says `equivalence` (in a route too)
  for `lenses`, writes each column's `facts` as its text alone, with
  `not_null` listing the columns proved never NULL, and a postcondition's
  `needs` as their tables and labels; format 4 writes `facts` as objects
  (text, nullability, bounds) and `needs` as whole `needed` objects.
- a report of format 2 or 3 and a manifest of format 1 or 2 say
  `"reference"` for the semantics 1.0 calls `"portable"` (`semantics`, and
  a route's `semantics`), and a reader maps it.

The OpenLineage facet `sverify_contract` follows the same name: its format
2 says `lenses` where format 1 said `equivalence`.

The report's JSON of format 1 was in no release, and `Report.from_json`
refuses it. Format 3 replaced `Report.proved` with `Report.verdict`: `verdict`
holds `proved`, `proved_with_checks` or `unproved`, where format 2 held the
report's first line, which `summary` holds now; `proved` stays, derived from
`verdict`, until 2.0. `Report.from_json` reads format 2 as well. In format 2 its postconditions, issues and assumptions take the
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
  again; for an export of a proved plan the report is proved. It proves each
  postcondition over the exported plan, shims included (#1484). An export whose
  postcondition's plan reads another relation, such as one written before #1484
  from a transformation that ends in a join's `select`, is refused with an error
  that says to verify and export again.

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
- an engine fact under [`engines/<engine>/facts/`](../engines/)
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

The public API is the names in the `__all__` of nine modules, `sverify`,
`sverify.io`, `sverify.engines`, `sverify.types`, `sverify.testing`,
`sverify.errors`, `sverify.cli`, `sverify.odcs` and `sverify.openlineage`,
and the members without a leading underscore of the classes among them.
Every type a public name returns, holds or takes is public too, so
`sverify.types` names the types a report and a refresh hold. The
[API reference](https://alexandernenninger.github.io/substrait-lean/)
documents each public name, and `tests/test_public_api.py` holds the
reference, the `__all__`s and that closure equal. Every other module is
internal, whether or not its name starts with an underscore, and so are
the maintainer tooling `sverify_dev` and the printed text of a report
(`str(report)`); tools read the report through its attributes or its JSON.
Three parts of `sverify.engines` are documented but outside the promise,
and may change in a minor release: the plan layer (`to_sql`,
`substrait_json`, `written_plan`, `delta_plans`), which takes sverify's
internal plan; `Dialect`'s SQL-writing methods and subclasses of it; and
the members of `Native`, while the native scans move into the engine
packages.
`Node.to_sql`, `Report.to_sql` and `Report.to_substrait` are the stable way
to a plan's SQL and Substrait.

The engine extension point is documented and outside the promise as well:
the entry-point group `sverify.profiles`, `ProfilePlugin` and the checker's
engine list (`EngineEntry`, `builtinEntries`,
[engine profiles from outside](engine-profiles.md#engine-profiles-from-outside))
may change in a minor release. A plugin checks `PLUGIN_API`, and an engine
package pins the sverify version it was built for. Custom sources and sinks
are the stable extension points.

The engines in the promise are those [Engines](#engines) lists.

A minor release may break the public API only when the break is:

- loud: a call that used the old form raises, or warns with a
  `DeprecationWarning`, and the message names the replacement;
- caught by a unit test that uses the old form;
- listed under "Breaking changes" in the changelog;
- given a migration note in that entry: what to write instead, with an
  example.

A renamed or removed name is gone in that release: sverify keeps no deprecated
alias. The old form raises, and the changelog entry names the replacement. A
release with breaking changes lists them first in its section of
[the changelog](../CHANGELOG.md).

## Engines

This section is the one statement of which engines sverify supports; other
pages link here. The reference is Lean's reference profile
([reference semantics](reference-semantics.md)), one of the profiles that
refine the core ([core, profiles and engines](core-and-profiles.md)), and an engine runs a plan
by a route that the checker justifies against it
([routes, classes and profiles](tasks.md#routes-classes-and-profiles)).

| Engine | Runs plans | Writes its SQL | Profile (`semantics=`) | Run proved sound by | In the 1.x promise |
|---|---|---|---|---|---|
| DuckDB | `engine="duckdb"`, the default | `dialect="duckdb"` | `"duckdb"` | `Engine.duckdb_sound`, under `Engine.NoRaiseSide` | yes |
| Polars, streaming | `engine="polars"` | | `"polars"` | `Engine.polars_sound`, under `Engine.GuardFreeSide` | yes |
| Spark 4.x | `engine="spark"` | `dialect="spark"` | `"spark"` | `Engine.spark_sound`, under `Engine.GuardFreeSide` | yes |
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

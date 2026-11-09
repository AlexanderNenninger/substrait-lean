# Engine characterization

What each engine does at each of the core's options
([core-semantics.md](../docs/core-semantics.md)), recorded as facts and
judged against sverify's reference. The engines' profiles
(`core/Sverify/Core/Profile.lean`, `PolarsProfile.lean`, `SparkProfile.lean`) and
their rows of the realizability table are built from these facts. Snowflake
behaviour is recorded privately.

## The directory

- [duckdb/](duckdb/README.md): the replay of DuckDB's sqllogictests (one
  ledger per area of DuckDB's `test/sql/`), the fuzz findings, the probes
  ([probes.json](duckdb/probes.json)), the facts and the DuckDB diff.
- Polars's facts and probes are in its engine package (#1189):
  [engines/polars/facts/](../engines/polars/facts/README.md) and
  [engines/polars/probes/](../engines/polars/probes/), under the in-memory and
  the streaming engine.
- Spark's facts, probes and fuzz findings are in its engine package (#1189):
  [engines/spark/facts/](../engines/spark/facts/README.md) and
  [engines/spark/probes/](../engines/spark/probes/).
- [oracle-a/benchmarks.json](oracle-a/benchmarks.json): each benchmark
  query's stage (`lift.STAGES`) when last written, which oracle A
  (`sverify_dev.oracle`) reads.
- `<engine>/facts/`: the facts, one JSON document each; an engine package
  keeps its own in `engines/<engine>/facts/` (`sverify_dev.facts.facts_dir`).
- [fact.schema.json](fact.schema.json): the facts' format.
  `python -m sverify_dev.facts` checks every document against it, and
  `tests/test_facts.py` does too.
- [areas.json](areas.json): the characterization checklist, area by area.
  Each fact names the items it settles in its `options`, and
  `python -m sverify_dev.facts --coverage <engine>` lists, per item, the
  engine's facts that settle it, or `missing`.

## What a fact is

A fact is one behaviour of one engine version (`engine`, `engine_version`):
what the engine does (`description`), what Substrait and sverify's reference
semantics do (`reference`), the settings it holds under, and its `status`:

- `deviation`: Lean disagrees with the reference;
- `fixed`: it did and no longer does;
- `decided`: an open choice, now decided;
- `shimmed`: the engine needs sverify's SQL to rewrite it;
- `no-finding`: the engine or Lean already gives the reference;
- `open`: undecided, where the engine differs from the reference and the
  profile has not decided how to bridge it;
- `workaround`: (io) the engine needs settings or a usage the fact gives.

Facts are written by hand from the evidence. A fact's `provenance` lists each
check: when, by which method and tool, and its evidence (a test at the
engine's commit, a ledger, a probe construct, a SQL repro with its output).
Its `evidence` is the strongest check in the provenance, weakest first:

1. `docs`: the engine's documentation;
2. `source`: its source at the release tag;
3. `engine_test`: the engine's own tests with an expected result, at the tag
   (DuckDB's sqllogictests, Polars's unit tests), read or replayed;
4. `probe`: edge cases run on the engine (probes, replays, repros);
5. `fuzz`: differential fuzzing against the reference;
6. `proof`: a Lean lemma covers it.

A fact that no longer holds (a new engine version) gets a new document with
`supersedes`, and the old one `superseded_by`. The `engine-fact` skill
(`.claude/skills/engine-fact/SKILL.md`) has the recipe.

## How the facts are judged

The reference model's principles (#185, "Principles for the reference
model"):

- `Rel.eval` means Substrait's semantics: each function's extension
  YAML, including its options.
- Where Substrait leaves a choice open, the reference raises if engines
  disagree on an edge case, and otherwise takes the least surprising value
  every backend can emulate
  ([Terminology](../docs/core-semantics.md#terminology)).
- An engine's profile refines the loose core; its diff against the
  reference is its row of the realizability table.

Substrait here is the spec at `v0.106.0`, the `substrait-extensions` package
`python/uv.lock` pins: `extensions/functions_arithmetic.yaml`,
`functions_comparison.yaml`, `functions_string.yaml` and the rest.

Where a plan omits a function option, the reference's defaults apply, as
decided on #185 ("Decided: what the reference does when a plan omits an
option"):

- an omitted `overflow` is ERROR, at the declared width `i8`…`i64`
  (`SILENT` and `SATURATE` only when the plan asks);
- an omitted `on_division_by_zero` is ERROR, for `divide` and
  `modulus` (`NULL` only when the plan asks);
- an error means "may raise", and a rewrite is proved as a refinement:
  it may raise in fewer cases, never answers differently, and never raises
  where the original did not.

In sverify, "may raise" is `verify`'s error issues (`Rel.mayIssues`,
`analysis/Sverify/Analysis/Safety.lean`): on a row where an error issue fires,
`Rel.eval`'s value is not the answer. So a finding is a deviation when
`Rel.eval` and `verify` together disagree with the reference: either
`Rel.eval` gives a different answer on a row where nothing may raise, or
`verify` calls an error a warning, or misses it. It is no finding when
`verify` reports the error that the reference raises.

For each finding, an engine's diff says whether the engine, under the
settings the fact records, gives the reference result natively, needs a
shim, or must be refused.

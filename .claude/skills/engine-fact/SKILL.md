---
name: engine-fact
description: Record what an engine does (overflow, NaN, casts, aggregate algorithms, ties) as an engine fact in characterization/<engine>/facts/ (engines/<engine>/facts/ for an engine package): id, fields, provenance, evidence order, rows, supersession, and the checker. Use when probing, fuzzing or researching DuckDB, Polars, Spark or Snowflake behaviour, or when a test or replay shows an engine differs from the reference.
---

# Engine facts

What an engine does (overflow, NaN, casts, the algorithm behind `VARIANCE`, …)
is recorded as facts, one JSON document per finding:
`characterization/<engine>/facts/<id>.json` (`duckdb/`, `spark/`, …), or, for
an engine that is a package of its own (#1189), `engines/<engine>/facts/<id>.json`
(Polars: `engines/polars/facts/`, its probes in `engines/polars/probes/`);
`sverify_dev.facts.facts_dir(engine)` says which. The format is
`characterization/fact.schema.json`'s. Every engine's research goes there,
whoever does it.

- The id is the engine and a number or slug (`duckdb-R5`,
  `polars-var-algorithm`); the file is named after it.
- Say what the engine does (`description`), at which exact `engine_version`,
  under which `settings`, and what the reference semantics does
  (`reference`), with a `status`.
- `provenance` lists each check: `checked_at` (the date), `method` (probe,
  source-reading, docs, replay, fuzz, manual-repro), `checked_by` (the tool,
  session or commit) and `evidence`: source links at a tag or commit, a SQL
  repro with its `observed` output, a test id, or a file of the repository
  (a ledger, or a construct of `probes.json`). Write "unknown" for what you
  can't recover; never guess a date or version.
- `evidence` is the strongest check in `provenance`: `docs` < `source` <
  `engine_test` (the engine's own tests with an expected result, at the
  release tag: DuckDB's sqllogictests, Polars's unit tests, Spark's golden
  files; method `engine-test`, or `replay` through `sverify_dev.slt`) <
  `probe` (probes, repros) < `fuzz` < `proof`. Research goes in that
  order, the cheaper kinds first. For Spark, `sverify_dev.spark_tests`
  searches the golden files and checks the links, and `sverify_dev.spark_fuzz`
  fuzzes the open deviations against a model of each fact.
- `rows` names the rows of the engine choice tables the fact settles: a
  function group of `Functions.lean`, one of its options, and only the types
  its checks covered. `python -m sverify_dev.facts --coverage <engine>` lists
  each row's facts, or `missing`, then the checklist's areas as a rollup.
- A new check of an old fact adds to its `provenance`. A fact that no longer
  holds (a new engine version) gets a new document with `supersedes`, and the
  old one `superseded_by`.

`python -m sverify_dev.facts` checks the documents (`tests/test_facts.py`
does too). The JSON documents are the record: there is no generated overview. The judging principles and the
DuckDB diff table are in `engines/duckdb/facts/README.md`.

Snowflake's facts are private: they live in `AlexanderNenninger/sverify-snowflake-evidence`, never in this repository. This repository gets only sverify's own Snowflake SQL fixes, citing "Snowflake behaviour recorded privately".

---
name: upstream-report
description: Draft or revise an upstream bug report for an upstream bug in `upstream/bugs/<ID>.json` (SQLGlot, DuckDB, DataFusion, Spark, Polars, Ibis, delta-rs, Substrait: its tooling and spec gaps), as bullet points the author writes up in their own words, or as full text when asked. Also for community posts about a bug or proposal (forums, Discord, Reddit). Use when asked to write, polish, check or prepare a report or issue for a bug ID (e.g. "write up SG-5", "draft the DuckDB issue for DD-3", "is DF-4 ready to file?"), or to check a report against a project's contributing guide. Covers provenance, duplicate and main-branch checks, the repro script, each project's issue form, and the voice the reports are written in.
argument-hint: "Bug ID(s), e.g. SG-5 or DF-4 DF-10"
---

# Upstream bug reports

The upstream bugs (`upstream/bugs/<ID>.json`, one document per bug, in the format of `upstream/bug.schema.json`) record what sverify found upstream. A report turns one document into an issue the author files by hand. Reports live in `../sverify-upstream-reports/` (one `<ID>-<project>.md` per entry, repro scripts in `repros/<ID>.py`, and a `README.md` with the status of every entry). If that folder is missing, ask where to put them.

**Never file an issue, comment, or react upstream.** Draft only; the author files.

## 1. Establish what happened

Read the document `upstream/bugs/<ID>.json`: `version`, `repro`, `handling`, the links in `upstream`, `issues` and `prs`, and `found_by`. That field decides how the report says the bug was found. Don't guess or embellish:

- "sqllogictest replay", "replay", `<file>.test`: DuckDB's sqllogictest suite replayed through `python/tools/sverify_dev/slt.py`, compared against the formalization.
- `fuzz__*.json` ledgers: the Hypothesis fuzzer (`sverify_dev/duckdb_fuzz.py`). **Only** these may be called fuzzing.
- `probes.json`, `duckdb-R15-*` facts: the function probe (`sverify_dev/probe.py`).
- `engines/<engine>/facts/`: characterizing the engine against the formalization.

If the source is unclear, check `git log -S'<ID>'` and the PR named in the document, then ask.

## 2. Check it is still a bug, and not known

1. **Latest release.** Run the repro on the latest release of the project (and its nightly where one exists). Record exact versions.
2. **Main.** Check whether `main` already fixes it: read the relevant code on `main` (`gh api repos/<owner>/<repo>/contents/<path>?ref=main`), and look at recently merged PRs touching that file. A fix for a *different* issue can cover this one (DataFusion #23468 fixed #17910 and also dedupes repeated grouping keys, which likely covers DF-4). SQLGlot's template explicitly asks to check main.
3. **Duplicates.** Use `gh issue list -R <repo> --state all --search "<terms>"` with several phrasings. `gh search issues` returned nothing for terms that do match, so don't rely on it alone.
4. **Cited numbers.** `gh issue view` / `gh pr view` every `#N` the report cites and check it says what the report claims.

Building another project's code runs it on the author's machine: ask first. DataFusion's substrait crate needs `protoc` (`brew install protobuf`), or `cmake` for the `protoc` feature.

## 3. Repro script

`repros/<ID>.py`, runnable with `uv run --no-project --with <pkg>==<version> python <ID>.py` (put that line at the top as `# Run: …`, as `repros/DF-4.py` does). It prints the library versions first, then each case. The report shows the script and its output in **separate** code blocks, with the exact versions the output came from. No `>>>` or `D` prompts.

Prefer end-user-visible behaviour (wrong rows, a failed round trip, a rejected plan) over internals; internals may follow as supporting evidence.

Fill the form's log and version fields with real output, captured in the same environment as the example's output: never leave a `<… output>` placeholder for them. Polars: run the report's example with `POLARS_VERBOSE=1` and paste its stderr under "Log output" (even when it only shows the runtime setup), and paste `pl.show_versions()` under "Installed versions".

## 4. Voice

- **First person singular.** "I", never "we", "us" or "our" (the author built sverify alone). Leave "we" inside quotes from other sources.
- **Friendly, not deferential.** A short thanks up front, naming something specific where there is one ("Thanks for SQLGlot, and for adding DuckDB's underscore separators in #4777!").
- **Short titles.** Under about 80 characters: the component, then the symptom ("qualify: HAVING resolves a name to the projection alias instead of the input column"). Examples, versions and the list of affected engines go in the body.
- **Ask for nothing.** No "please close / relabel / confirm / say if deliberate / let me know". State facts; maintainers decide. (A project form's own fixed wording, like DataFusion's willingness dropdown, is fine.)
- **No self-doubting hedges** ("I may be misreading"). State what was checked and what wasn't ("ClickHouse shares the flag; I haven't checked its rule").
- **Not terse.** Keep the explanation, the expected result with its reasoning, and where the cause is in the code. Drop pleasantries at the end.
- **Don't name sverify.** Say how it was found, and link the word *formalization* to `https://github.com/AlexanderNenninger/substrait-lean`. Describe the formalization by what the reader cares about:
  - DuckDB and SQLGlot: "a [formalization](https://github.com/AlexanderNenninger/substrait-lean) of parts of DuckDB's SQL semantics" (the DuckDB profile is the diff to the Substrait core).
  - Substrait producers and consumers (DataFusion, substrait tooling): "a [formalization](https://github.com/AlexanderNenninger/substrait-lean) of Substrait plan semantics".

  For example: "I found this inconsistency while replaying DuckDB's sqllogictest suite through SQLGlot's `qualify` and comparing the results against a [formalization](https://github.com/AlexanderNenninger/substrait-lean) of parts of DuckDB's SQL semantics."

### Bullets, not prose

The author writes the words. By default a draft is a list of bullet points in the order the text will run (thanks, how it was found, the case, expected and actual, the cause in the code, the proposal or question), each one fact with its link, version or snippet. The author turns them into sentences in their own voice. The parts that must be exact stay complete: the title suggestion, the repro script, code blocks, tables, versions and conformance cases.

The same holds for anything the author posts in a community (a forum or Discord thread, a mailing list, Reddit, a talk abstract) about a bug or a proposal: give the points and the links, not a finished post. Write full prose only when the author asks for it. The voice rules above apply to the bullets' content: facts stated plainly, nothing asked for, no hedges.

## 5. Each project's rules

Each project's code of conduct, contributing guide, issue form, AI policy and triage habits are summarised in `../sverify-upstream-reports/guidelines/<project>.md` (`sqlglot`, `duckdb`, `datafusion`, `spark`, `polars`, `ibis`, `delta-rs`, `substrait`), with sources pinned to the commits read and a drafting checklist at the end; `guidelines/README.md` compares them. Read the project's note before drafting. If it is more than a few months old, or the project's template has changed (`gh api repos/<repo>/contents/.github/ISSUE_TEMPLATE`), recheck the files it cites and update the note.

What changes the draft itself, as of 2026-11-04:

- **The author's own words.** DuckDB, Polars and Ibis don't accept AI-written issue text. For them the draft is the reproduction, the facts and short notes, and the author writes the prose. DuckDB allows AI context only as a disclosed `>` quote; Polars wants a disclosure line naming the tool and its extent; at Ibis a `maybe-ai` label closes the issue. SQLGlot, DataFusion, delta-rs and Substrait accept a draft the author reviews; Substrait wants one sentence on the tools used.
- **Personal fields.** DuckDB requires Full Name and Affiliation: leave `<your full name>` / `<your affiliation>` placeholders and tell the author. Spark takes bugs in ASF JIRA (SPARK), under an account in the author's real name, in wiki markup (`{code:sql}`), with Issue Type, Priority, Component and Affects Version; its GitHub issues are an experiment that auto-closes after 100 idle days.
- **Where it goes.** DuckDB's clients and extensions have their own repos (`duckdb-python` has its own form); Ibis's Substrait producer is `ibis-project/ibis-substrait`; Substrait's spec issues go to `substrait-io/substrait`, tooling bugs to the library's repo, quoting the spec text that defines the expected result.
- **Spec gaps** (`kind: spec-gap`, `ST-<n>`): an issue in `substrait-io/substrait` with the YAML file and line at a commit, concrete calls with their types, what each engine does (versions, facts), a proposal reusing existing option names, alternatives and whether it is breaking; then, once someone responds, a small `feat(extensions):` PR changing the YAML with `tests/cases/*.test` (the PR needs the CLA). Search for an existing issue first and comment there instead.
- **Pacing.** File one report at a time, spread over days: DataFusion labels accounts that file many reports quickly.
- **Forms.** SQLGlot: state the read and write dialects and check main. DataFusion: the willingness answer is "I would like to contribute a fix for this bug, but request guidance from the DataFusion community"; spec-like requests use the feature form. Polars: the `POLARS_VERBOSE=1` log and `pl.show_versions()` output filled in (section 3), and keywords in the title set the area label. delta-rs: `deltalake.__version__` and `deltalake.rust_core_version()`.

### Spec-gap proposals (#1093)

A spec gap goes upstream as a proposal with the formal reading attached, so the discussion starts from a definition. The draft (`ST-<n>-substrait.md`) has five parts, in this order, each as bullets ("Bullets, not prose" above) except the tables, diffs and cases:

1. **The gap**: the YAML or spec file and lines at the commit checked (re-check `main` and the latest release the day of drafting), and the question in one paragraph, with the calls and types (`subtract(inf::fp64, inf::fp64)`) or the plan (a `SortRel` field with `SORT_DIRECTION_UNSPECIFIED`) that exposes it.
2. **What engines do**: a table from the entry's `facts` ids, DuckDB, Spark and Polars with their versions, plus engines another thread already cites. Leave out Snowflake. Leave out DataFusion, except as a recorded engine. Where an engine's docs are silent, say each cell comes from running the engine. A cell derived from a fact that did not run the exact case goes in the author's notes as such.
3. **The readings**: the formalization's, in its words (the core's open option, and the reference's choice), with the alternatives. The draft names no D-number or Lean name; the author's notes give the D-number and the `docs/core-semantics.md` option for checking.
4. **The proposed text as a diff**: reuse an existing option name and its values (`on_domain_error`, `overflow`, `rounding`) before inventing one, and say whether the change is breaking under Substrait's policy.
5. **A conformance case** in Substrait's `.test` format (`func(args) [option:VALUE] = result`, as `tests/cases/arithmetic/multiply.test` writes options), or for a relation, the plan and its expected rows or rejection.

Where an upstream thread already asks the question, the draft is a comment there, and adds what the thread lacks: an engine that disagrees, a case it misses. A section "For the author" ends every draft: what was not verified, the facts behind each cell, the formalization's D-number, and where the draft comes in #1093's order. When the draft is written, add a `checked` entry to `upstream/bugs/ST-<n>.json` with the commit checked, and update the row in the reports `README.md`.

## 6. Finish

- Once the author has filed it, update `upstream/bugs/<ID>.json` in the repository: `status` `filed`, the link in `upstream` and `status_note`, and a new `checked` entry with the versions the report was checked on. `python -m sverify_dev.bugs` checks the document.
- Update the reports `README.md`: the entry's row, and a "Worth a look" line for anything unverified (e.g. "may be fixed on main by #N; not tested").
- Tell the author what still needs them: placeholders to fill, form fields to pick, anything not verified, and whether a duplicate or main-branch fix was found.
- Keep the thread current. An entry with an open thread (`filed`, or a `duplicate`) gets a `checked` entry at least every 90 days: look at the upstream thread, record its state in `status` and `status_note` (a fix: `fixed upstream` with `fixed_in`), and add the `checked` entry with the versions. The `ledger` job warns (`sverify_dev.bugs --stale`) on a thread not checked in 90 days. `upstream/REPORT.md` ("Filed and fixed") updates on main from these fields.

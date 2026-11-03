---
name: upstream-report
description: Draft or revise an upstream bug report for an entry in `upstream/LEDGER.md` (SQLGlot, DuckDB, DataFusion, Ibis, delta-rs, Substrait tooling), ready for the author to file. Use when asked to write, polish, check or prepare a report or issue for a ledger ID (e.g. "write up SG-5", "draft the DuckDB issue for DD-3", "is DF-4 ready to file?"), or to check a report against a project's contributing guide. Covers provenance, duplicate and main-branch checks, the repro script, each project's issue form, and the voice the reports are written in.
argument-hint: "Ledger ID(s), e.g. SG-5 or DF-4 DF-10"
---

# Upstream bug reports

The ledger (`upstream/LEDGER.md`) records what sverify found upstream. A report turns one entry into an issue the author files by hand. Reports live in `../sverify-upstream-reports/` (one `<ID>-<project>.md` per entry, repro scripts in `repros/<ID>.py`, and a `README.md` with the status of every entry). If that folder is missing, ask where to put them.

**Never file an issue, comment, or react upstream.** Draft only; the author files.

## 1. Establish what happened

Read the ledger row: version, minimal repro, workaround, and the **Found by** column (where the section has one). That column decides how the report says the bug was found. Don't guess or embellish:

- "sqllogictest replay", "replay", `<file>.test`: DuckDB's sqllogictest suite replayed through `python/tools/sverify_dev/slt.py`, compared against the formalization.
- `fuzz__*.json` ledgers: the Hypothesis fuzzer (`sverify_dev/duckdb_fuzz.py`). **Only** these may be called fuzzing.
- `probes.json`, `duckdb-R15-*` facts: the function probe (`sverify_dev/probe.py`).
- `characterization/<engine>/facts/`: characterizing the engine against the formalization.

If the source is unclear, check `git log -S'<ID>'` and the PR named in the row, then ask.

## 2. Check it is still a bug, and not known

1. **Latest release.** Run the repro on the latest release of the project (and its nightly where one exists). Record exact versions.
2. **Main.** Check whether `main` already fixes it: read the relevant code on `main` (`gh api repos/<owner>/<repo>/contents/<path>?ref=main`), and look at recently merged PRs touching that file. A fix for a *different* issue can cover this one (DataFusion #23468 fixed #17910 and also dedupes repeated grouping keys, which likely covers DF-4). SQLGlot's template explicitly asks to check main.
3. **Duplicates.** Use `gh issue list -R <repo> --state all --search "<terms>"` with several phrasings. `gh search issues` returned nothing for terms that do match, so don't rely on it alone.
4. **Cited numbers.** `gh issue view` / `gh pr view` every `#N` the report cites and check it says what the report claims.

Building another project's code runs it on the author's machine: ask first. DataFusion's substrait crate needs `protoc` (`brew install protobuf`), or `cmake` for the `protoc` feature.

## 3. Repro script

`repros/<ID>.py`, runnable with `uv run --no-project --with <pkg>==<version> python <ID>.py` (put that line at the top as `# Run: …`, as `repros/DF-4.py` does). It prints the library versions first, then each case. The report shows the script and its output in **separate** code blocks, with the exact versions the output came from. No `>>>` or `D` prompts.

Prefer end-user-visible behaviour (wrong rows, a failed round trip, a rejected plan) over internals; internals may follow as supporting evidence.

## 4. Voice

- **First person singular.** "I", never "we", "us" or "our" (the author built sverify alone). Leave "we" inside quotes from other sources.
- **Friendly, not deferential.** A short thanks up front, naming something specific where there is one ("Thanks for SQLGlot, and for adding DuckDB's underscore separators in #4777!").
- **Ask for nothing.** No "please close / relabel / confirm / say if deliberate / let me know". State facts; maintainers decide. (A project form's own fixed wording, like DataFusion's willingness dropdown, is fine.)
- **No self-doubting hedges** ("I may be misreading"). State what was checked and what wasn't ("ClickHouse shares the flag; I haven't checked its rule").
- **Not terse.** Keep the explanation, the expected result with its reasoning, and where the cause is in the code. Drop pleasantries at the end.
- **Don't name sverify.** Say how it was found, and link the word *formalization* to `https://github.com/AlexanderNenninger/substrait-lean`. Describe the formalization by what the reader cares about:
  - DuckDB and SQLGlot: "a [formalization](https://github.com/AlexanderNenninger/substrait-lean) of parts of DuckDB's SQL semantics" (the DuckDB profile is the diff to the Substrait core).
  - Substrait producers and consumers (DataFusion, substrait tooling): "a [formalization](https://github.com/AlexanderNenninger/substrait-lean) of Substrait plan semantics".

  For example: "I found this inconsistency while replaying DuckDB's sqllogictest suite through SQLGlot's `qualify` and comparing the results against a [formalization](https://github.com/AlexanderNenninger/substrait-lean) of parts of DuckDB's SQL semantics."

## 5. Each project's form

Fetch the current template before writing (`gh api repos/<repo>/contents/.github/ISSUE_TEMPLATE`), plus `CONTRIBUTING.md` and the code of conduct; they change. As of 2026-11:

**SQLGlot** (`tobymao/sqlglot`, `bug_report.md`): `Title:` line, intro paragraph, `## Fully reproducible code snippet` (state the read and write dialects), `## Official Documentation` (links), optionally `## Where it comes from`. Check main first.

**DuckDB** (`duckdb/duckdb`, `bug_report.yml`): `### What happens?` (short, clear and concise: thanks, how found, the symptom; put the cause analysis further down), `### To Reproduce`, `### OS:` (with architecture), `### DuckDB Version:`, `### DuckDB Client:`, `### Hardware:`, `### Full Name:`, `### Affiliation:`, then the three checklist questions. Full Name and Affiliation are **required**: DuckDB may close issues without them. Leave `<your full name>` / `<your affiliation>` placeholders and tell the author. Client and extension bugs go to their own repos (the form lists them). Mention whether the repro is plain SQL that runs in the CLI.

**DataFusion** (`apache/datafusion`, `bug_report.yml`): `### Describe the bug`, `### To Reproduce`, `### Expected behavior`, `### Additional context`, `### Willingness to contribute`. The author's answer for willingness is "I would like to contribute a fix for this bug, but request guidance from the DataFusion community". ASF Code of Conduct. Its AI policy (`docs/source/contributor-guide/ai-policy.md`) asks for a clear problem statement and a minimal repro focused on user-visible behaviour, and expects the author to discuss it in their own words.

Other projects: follow their template the same way and add them here.

## 6. Finish

- Update the reports `README.md`: the entry's row, and a "Worth a look" line for anything unverified (e.g. "may be fixed on main by #N; not tested").
- Tell the author what still needs them: placeholders to fill, form fields to pick, anything not verified, and whether a duplicate or main-branch fix was found.

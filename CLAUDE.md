# Notes for Claude

## Every PR leaves its area faster and simpler

Each pull request comes with two improvements in the area it touches,
beside its main change: one to performance and one to code quality.

Performance, one of these:

- Faster development: a quicker or leaner build, test, proof or check. For
  example, a slow test made cheap, a `decide` replaced by reflection, a
  smaller generated module or a cached step.
- Faster at runtime: sverify running faster or in less memory for its users.
  For example, a smaller written plan, a cheaper proof, less data read or a
  lower peak.

Code quality, one of these:

- Simpler code:
  - less code for the same behaviour, such as dead code, a duplicate helper
    or a table kept in two places;
  - fewer special cases, such as engine shims, refusals, per-engine
    branches, strict xfails or flags;
  - one source of truth, a fact written once and derived where it's needed.
- Stronger proofs:
  - fewer assumptions: a hypothesis dropped, a trusted axiom proved, or a
    side condition made a decidable check;
  - one general lemma in place of several;
  - a type that rules out a wrong state.
- Better structure:
  - uniform terminology and API: one name for one concept across Lean,
    Python, docs and messages, and one shape for calls that do alike
    things (parameter names, order, return types);
  - a public API with fewer names or parameters;
  - less import fan-in, or a cycle broken;
  - a large module split along its seams. A split counts only when the file
    has more than 1,500 lines and each part keeps at least 300. Tiny
    modules don't count.

Measure both, before and after, and put the numbers in the PR body under
"Improvement", one line for each. Count lines, shims, xfails, hypotheses,
axioms, public names, names for one concept, seconds or bytes, whichever
fits. Keep them in the code the PR already touches, so they don't collide
with other sessions' work. A PR that touches nothing measurable (docs,
facts, ledgers) says so instead, and a PR whose area has no runtime or
build cost to cut says which of the two it couldn't find.

Behaviour stays the same: an improvement changes no result and weakens no
proof. Shorter must also stay clear. Golfed code or a cryptic proof doesn't
count.

## Running QA

`poe qa` (from `python/`) runs everything: Lean proofs, build, lint,
typecheck, golden tests and every Python test (`poe test-all`). It is slow on
this laptop.

Locally, run `poe test`: the fast set on 2 workers, without the `slow` tests
and with a tenth of the Hypothesis examples (the `dev` profile,
`python/tests/conftest.py`). Leave the full suite to CI or to homelab
(`homelab_qa.sh` runs `qa`). CI runs every test with the full counts, `core`
in three shards.

Before every push, run the cheap checks from `python/`: `poe fmt` (ruff's fixes
and formatting, also of the notebooks), then `poe lint` and `poe typecheck`
(pyrefly). They take seconds and catch what CI's `static` job would fail on.
Call them as `.venv/bin/poe …` (or `.venv/bin/ruff`, `.venv/bin/pyrefly`):
`uv run` may rebuild the package, and its build hook runs a full `lake build`
that races any build already running. A worktree without a venv can use
another worktree's tools. A push that changes Lean also builds with
`lake build --wfail` first.

On pull requests CI runs what the change can affect; pushes to main, merge
queue entries and retargets run everything. One job builds `substrait-check`
and the others download it. The generated proofs are checked only when a
Lean input changes. Engine jobs, oracle A and the notebooks skip changes in
areas they cannot read (the table in the `changes` job), `dbt/` among them. A pull request that
changes only facts, probes, `upstream/` or `python/tests/lift_backlog.json`
(and docs) runs `static` and a `ledger` job: the checkers and the tests that
read those files. A pull request into a branch other than main or a release branch (a stack)
runs `static` only and its `qa` fails; retargeting it to main starts the full
run (`.github/workflows/retarget.yml`). The header of
`.github/workflows/ci.yml` has the details.

A pull request that changes `python/` also runs `outside-repo`: the fast set
from a copy of the tests outside the repository, as the release's wheel test
runs them (`python/scripts/wheel_tests.sh`). A test that reads repository
files (docs, the catalogue, facts, Lean sources) carries `needs_repo`
(`tests/_repo.py`); a test dependency the package doesn't bring goes into
that script's list, or the test uses `pytest.importorskip`. Run it locally
with `bash python/scripts/wheel_tests.sh --editable python --fast`.

### Releases

Main never freezes for a release. A release is cut as a branch,
`release/<major>.<minor>`, which CI treats like main; the version bump, the
release's fixes and the tag happen there, and the branch is merged back into
main afterwards (`.claude/skills/release-sverify/SKILL.md`). Keep merging into
main meanwhile.

### Runner slots

GitHub runs at most 20 jobs at once for this repository, and a full CI run
is about 25. Every push to a pull request queues a new run, so many open
pull requests wait on each other.

- Merge main into your branch only when the pull request conflicts, or when
  the coordinator asks before merging it. Merging main after every push
  restarts the whole run for nothing.
- Push finished work in one push, not a commit at a time while CI runs.
- The coordinator merges through batches: green pull requests merged into
  one branch, one CI run, then merged into main. A push to main whose tree
  a passing pull request run already tested runs `static` only (the header
  of `ci.yml`). Docs builds on a pull request only when it changes a file
  the site reads.

### Check capacity before expensive tasks

Several agents often work at once, and together they have crashed the
laptop. Start an expensive task (`poe qa`, `lake build`, the full pytest
suite, notebook runs, wheel builds) only when the machine it runs on has
spare capacity. This applies to the laptop as much as to `homelab`.

- **Laptop** (10 cores, 16 GB RAM): check `uptime` and `memory_pressure | tail -1`.
  If the 1-minute load average is above 6, or free memory is below 30 %,
  don't start the task. Wait and check again, or run only the tests your
  change touches.
- **Long checker runs never run on the laptop.** A `substrait-check` that works
  through many plans (`snowflake_plan_fuzz compare`, replays, fuzzing) can
  grow past the laptop's memory in seconds, while the load average stays low.
  On 2026-11-07 one reached 23 GB and hung the laptop twice (#1074). Run
  these on homelab under `homelab_qa.sh`'s memory cap. Locally, run only a
  small slice, one plain checker call at a time, under a watchdog that kills
  a checker above 4 GB of RSS: macOS refuses `ulimit -v`.
- **homelab**: see below.

Editing `python/pyproject.toml` (or `uv.lock`) makes the next `uv run` rebuild
the package, and its build hook runs a full `lake build`. After such an
edit, run tools through `python/.venv/bin/` directly, or check capacity
first as for any build.

Run one expensive task at a time per agent, never several in parallel.
`poe test` caps itself at 2 workers; `poe test-all` and the per-backend tasks
use `pytest -n auto`, which takes every core. On the laptop, run pytest
directly with `-n 2` instead.

For long QA runs, use `homelab` (`ssh -o BatchMode=yes homelab`, over
Tailscale; Pop!_OS, 12 cores, 15 GB; elan and uv in `~/.elan/bin` and
`~/.local/bin`, which a non-interactive `ssh` does not put on `PATH`). It
has no GitHub push credentials, so push your branch first, then run, in the
background, from the repository root:

```bash
ssh homelab 'bash -s -- <branch>' < python/scripts/homelab_qa.sh
```

The script clones the branch into `/tmp/substrait-lean-<uuid>`, reuses a
warm Lean build, runs `poe qa` (or the poe tasks named after the branch)
under memory caps, and deletes the directory at exit. Its header documents
its options. Several agents and the user's own services share the box, and
two parallel runs once hung it, so check first:

```bash
ssh homelab 'nproc; uptime; free -g | sed -n 2p; ls -d /tmp/substrait-lean-* 2>/dev/null | wc -l'
```

- **One run at a time.** A `/tmp/substrait-lean-*` directory means a run is
  going. Long jobs that aren't QA (a replay, fuzzing, TLC) count too: give
  them such a directory. The chaos run (the `chaos-run` skill) is the one
  exception.
- **Don't start** above a 1-minute load of 8, or with less than 6 GB
  available. Cap workers with `PYTEST_XDIST_AUTO_NUM_WORKERS=2`, the
  script's default, and run under `nice -n 10`.
- **Never use sudo there,** not even `sudo -n`. Nothing in QA needs root;
  if something seems to, stop and ask the coordinator.
- **Clean up:** delete your directory when the run ends, also when it fails.
  Stop a run by PID (SIGTERM to the script's bash), never `pkill -f` over
  `ssh`: the pattern matches the `ssh` command itself. A crashed session can
  leave a directory behind; if no process uses it, remove it.

## Working beside other sessions

Several Claude sessions work in this repository at once, steered by a
coordinator session that assigns work and merges PRs through batches.

- **Stay in your task's files.** If something outside them needs changing,
  tell the coordinator instead of changing it; another session may own it.
- **At most three sessions build or test at once.** The coordinator holds
  the rest; seven parallel Lean builds once took the Claude app down.
- **Report, don't wait silently:** message the coordinator when a PR is
  ready, when you're blocked, or when a planned step turns out wrong.
- **Shell loops that wait on another process** match by PID. A `pgrep -f`
  pattern also matches the shell running it, and waits forever.
- **After resolving a merge conflict,** run the tests of every file you
  resolved, not only your own change's. A resolution can drop the other
  side's code silently (#1066 lost a flag that way), and a Hypothesis case
  it breaks is saved and then fails on every branch.

## Lean proofs

### The design, in one picture

`docs/core-semantics.md` ("Terminology") is the source; this is the summary
every session should hold before it touches `SubstraitLean/`.

- The core (`Rel.eval`, `Rel.Allowed`, the options) is an abstract machine.
  It runs no plan. Every point where engines or Substrait differ is an open
  option, so the core can simulate every supported behaviour by narrowing
  its options. A profile is the core with its options narrowed.
- The reference profile (`Profile.reference`) is one profile among the
  others, separate from the core. Plans are verified under it. It is strict
  where engines disagree (it raises), and where it picks a value it picks one
  every engine gives natively or with a cheap shim. It belongs to no engine.
- Each engine has a profile of its own (`Profile.duckdb`, Polars, Spark,
  Snowflake), stating what that engine computes, from
  `characterization/<engine>/facts/`. Engine profiles are siblings: none
  refines another, and none refines the reference. A plan verified under
  the reference reaches an engine through a translation (the lowering),
  shimmed only on the reference's value choices, and the engine's profile
  is what the lowered plan is evaluated under in `Engine.Sound`.
- Substrait has a profile of the same kind (`Profile.substrait`): the
  YAMLs' own looseness, a sibling of the reference, since the reference
  overrides Substrait in places.

What goes into the core. The core is the idealised setting and holds no
engine-specific workaround: no shim, no engine's quirk, no version-specific
behaviour, no branch on an engine's name. A behaviour enters the core only
as an option, and only when a tier-1 engine (DuckDB, Polars, Spark) needs
that option for its plans to be checkable, that is, when without it the
core could not state what that engine computes. Then the option is added
once, for every engine, with the reference's value for it recorded as a
decision. Everything else lives in the profiles: a single engine's
behaviour in its profile and facts, a translation in its lowering, a
compensation in its shims. If a change to `Rel.eval` or `Rel.Allowed`
mentions an engine, it is in the wrong place.

Two consequences. An engine's profile is an engine fact, never a choice:
defining one as `Profile.reference` (as `Profile.spark` is today) states a
verification semantics, not what Spark computes, and a theorem over it says
nothing about Spark (#271 replaces it). And a user-facing semantics
(`semantics="duckdb"`) is a choice of profile to verify under, a different
role from the engine profile the lowered plan runs under, even when the
two profiles share a name.

### The rules

The `prove-lean` skill has the workflow. The rules:

- No `native_decide`, no `sorry`, and `decide` only on small terms.
  `#print axioms` of the changed theorems stays as it was, or the PR says
  why it changed.
- Never weaken a theorem to make it pass. If a statement turns out false,
  say so, and propose the corrected statement with a side condition named as
  a predicate, as #899 did.
- The reference semantics (`Rel.eval`, `Rel.Allowed`, `docs/core-semantics.md`)
  changes only through a recorded decision (D-numbers in that doc).
- Where the reference leaves a choice open (tie order, float sums), prove
  membership in `Allowed`, not equality.
- CI builds the proofs with `--wfail`: a warning fails the build. A new
  module gets its line in `docs/proofs.md` (`tests/test_proof_map.py`).

## Engines

DuckDB, Polars, Spark and Snowflake are the 1.0 engines. DataFusion is an
optional engine and never a reference: Lean's model is the reference, and
DuckDB is the default oracle where tests compare against an engine.
Snowflake's facts are private (the `engine-fact` skill says where).

## Skills

Task recipes live in `.claude/skills/` and load when needed: `add-function`
(functions and coverage cases; older comments call it CLAUDE.md's "Adding
functions"), `engine-fact` (formerly "Engine facts"), `upstream-bug`,
`upstream-report`, `prove-lean`, `chaos-run`, `query-semantics` and
`release-sverify`.

## sverify-dbt

`dbt/` holds `sverify-dbt`, a package of its own on sverify's public API: it
checks a dbt project's tests and contracts (#177). It is released with
sverify at the same version, pinning `sverify==<version>` (#732; the release
skill bumps both), and its CI job (`dbt`) runs when `dbt/`, `python/` or the
Lean sources change. Where it needs something sverify's public API lacks, the
addition goes into sverify, and `dbt/API-NOTES.md` records it.

## Notebooks on molab

The README's molab links open `notebooks/` on the `published` branch, not on
`main`: molab reads notebooks straight from GitHub, and `main` runs ahead of
PyPI. After the PyPI upload of a `v*` tag, the `publish-notebooks` job of
`.github/workflows/wheels.yml` rewrites each notebook's PEP 723 header with
`python/scripts/publish_notebooks.py` (it drops the `[tool.uv.sources]` path to
`../python` and pins `sverify[...]==<version>`), runs each one against the
release, and commits the result to `published`, one commit per release. Never
edit or force-push `published`. To republish a release, start the workflow by
hand with `notebooks: <version>`; `dry_run: true` runs this ref's notebooks
against that version without pushing.

## Generated files

Don't commit regenerated tables on a feature branch. They are rewritten on
`main` after every merge by the `Generated files` workflow
(`.github/workflows/generated.yml`), so committing them only causes merge
conflicts with other PRs:

- `README.md`'s coverage table (`<!-- coverage:start -->` … `<!-- coverage:end -->`),
  from `sverify_dev.coverage --write-readme`;
- `catalogue/INDEX.md` and `catalogue/FINDINGS.md`'s stats tables, from
  `sverify_dev.catalogue --write-tables`;
- `docs/realizability.md`, from `sverify_dev.realizability --write`;
- `upstream/REPORT.md`, the upstream bugs to report and the count of each
  class, from `sverify_dev.bugs --write`.

Generated Lean modules are different: `SubstraitLean/LoweringDuckDB/On` (the
DuckDB lowering, for DuckDB's default settings only) and
`SubstraitLean/LiftDuckDB/Duckdb` and `Reference` (the lift from DuckDB SQL),
entries with their proofs, are committed, and a build only checks them. When a
build fails there, or a golden test of theirs changes, regenerate them with
`poe regen-lowering` or `poe regen-lift` and commit the result. Both cap Lean at
6 GB (`-M 6144`).

Their proofs are checked only when the lakefile's `check_generated` option is
on (`SubstraitLean/Generated.lean`). It is off by default, so a local
`lake build` takes the entries as proved and stays quick; the tables and their
staleness checks are the same. CI, the Wheels workflow, `poe prove` (and so
`poe qa`), `homelab_qa.sh` and the wheel's build hook turn it on with
`lake -R -Kcheck_generated=true build`. Lake keeps the setting of the last `-R`,
so after one of those, `lake -R build` goes back to quick builds. Turn it on
locally when you change a generated module, `Profile.duckdb` or the
generators' tactics.

If you ran one of these commands locally, `git checkout` those files again
before you commit. Edit the sources instead: the `CASES` of
`python/tools/sverify_dev/coverage_cases/<area>.py`, the catalogue's TOML, and
`catalogue/status.json`. `status.json` is not just output: it holds the results
`tests/test_catalogue.py` expects. So a PR that adds a catalogue query or
changes coverage commits it, after `sverify_dev.catalogue --write`.


## Voice

The READMEs, `docs/` and the tour's markdown cells (`notebooks/`) share one
voice: light, direct and concise.

- Sverify is the subject ("Sverify proves…"). Write "Sverify" at the start of
  a sentence and `sverify` for the package elsewhere.
- No bold, emojis, exclamation marks, "simply" or "just". Drop filler and
  hedges.
- No opposing pairs ("X, not Y", "proved, not tested", "instead of"). State the
  claim and stop.
- Claims about objective facts link to what supports them: a doc, test,
  issue, table or number.
- Keep every fact, identifier, link and number.

The tour's notebooks add three things for the data engineer with a stake in
the outcome:

- An opening of two or three sentences in the second person that sets the
  scene and the stakes (the customer charged twice, whoever gets paged at
  3 a.m.), then the rule or feature.
- Walkthrough steps say "we": "We'll write the rule in Ibis, state what it
  assumes and what it promises, and have the checker prove it before any data
  runs." Openings and recaps speak to the reader as "you".
- A closing paragraph about what the reader can now do, leading into the next
  notebook with its link. No humour.

An opening: "Say you're on the payments team. A customer was charged twice for
the same coffee, and by the time support hears about it, they've already
tweeted. You want to catch these double charges, the same card paying the
same amount at the same merchant twice within five minutes, and refund them
first."

## Changelog

Don't edit `CHANGELOG.md` in a feature PR: parallel PRs all conflict at its top.
Add one file to `changelog.d/` instead (see its README). The release folds the
fragments into `CHANGELOG.md`.



# Notes for Claude

## Running QA

`poe qa` (from `python/`) runs everything: Lean proofs, build, lint,
typecheck, golden tests and every Python test (`poe test-all`). It is slow on
this laptop.

Locally, run `poe test`: the fast set on 2 workers, without the `slow` tests
and with a tenth of the Hypothesis examples (the `dev` profile,
`python/tests/conftest.py`). Leave the full suite to CI or to homelab
(`homelab_qa.sh` runs `qa`). CI runs every test with the full counts, `core`
in three shards.

On pull requests CI runs what the change can affect; pushes to main, merge
queue entries and retargets run everything. One job builds `substrait-check`
and the others download it. The generated proofs are checked only when a
Lean input changes. Engine jobs, oracle A and the notebooks skip changes in
areas they cannot read (the table in the `changes` job). A pull request that
changes only facts, probes, `upstream/` or `python/tests/lift_backlog.json`
(and docs) runs `static` and a `ledger` job: the checkers and the tests that
read those files. A pull request into a branch other than main (a stack)
runs `static` only and its `qa` fails; retargeting it to main starts the full
run (`.github/workflows/retarget.yml`). The header of
`.github/workflows/ci.yml` has the details.

### Check capacity before expensive tasks

Several agents often work at once, and together they have crashed the
laptop. Start an expensive task (`poe qa`, `lake build`, the full pytest
suite, notebook runs, wheel builds) only when the machine it runs on has
spare capacity. This applies to the laptop as much as to `homelab`.

- **Laptop** (10 cores, 16 GB RAM): check `uptime` and `memory_pressure | tail -1`.
  If the 1-minute load average is above 6, or free memory is below 30 %,
  don't start the task. Wait and check again, or run only the tests your
  change touches.
- **homelab**: see below.

Run one expensive task at a time per agent, never several in parallel.
`poe test` caps itself at 2 workers; `poe test-all` and the per-backend tasks
use `pytest -n auto`, which takes every core. On the laptop, run pytest
directly with `-n 2` instead.

For long QA runs, use the `homelab` server for more compute: `ssh homelab`
(reached over Tailscale, user `nennia`, key auth, so `ssh -o BatchMode=yes`
works). It is Pop!_OS 24.04 (Ubuntu-based, so `apt`), x86_64, 12 cores,
15 GB RAM. elan and uv are installed in `~/.elan/bin` and `~/.local/bin`,
which a non-interactive `ssh` does not put on `PATH`. The box has no GitHub
push credentials, so to test local changes push a branch first.

Several agents share the box, and it also runs the user's own services (an
`ollama` model server among them, using several GB). Two parallel QA runs
once drove it to a load of over 100 and hung it. So check before starting
a run:

```bash
ssh homelab 'nproc; uptime; free -g | sed -n 2p; ls -d /tmp/substrait-lean-* 2>/dev/null | wc -l'
```

- **One QA run at a time.** If a `/tmp/substrait-lean-*` directory exists,
  another run is going: wait, or run only the tests your change touches
  locally. The background chaos run (below) is the one exception: it runs
  under `/tmp/substrait-chaos-*`, which this check leaves out, and one QA run
  may go alongside it.
- **Don't start** if the 1-minute load average is above 8, or if less than
  6 GB is available (the `available` column of `free -g`).
- **Cap the workers:** the poe test tasks use `pytest -n auto`, which takes
  every core. Set `PYTEST_XDIST_AUTO_NUM_WORKERS=4` so a run fits the 8 GB cap (6 workers peaked over it after #729; 4 peak at 7.8 GB) and leaves the
  box free.
- **Run under `nice -n 10`** so interactive use of the box stays responsive.
- **Long-running jobs that aren't QA** (a full sqllogictest replay, fuzzing)
  count as a run too. Give them a `/tmp/substrait-lean-*` directory, so the
  check above sees them.
- **Clean up after yourself.** Delete your directory when the run ends,
  also when it fails. To stop a run, kill its processes by PID, not with
  `pkill -f` over `ssh`: the pattern also matches the `ssh` command itself.

Each run gets its own directory,
`/tmp/substrait-lean-<uuid>`. Never run tests in a shared checkout such as
`~/Projects/substrait-lean`. `python/scripts/homelab_qa.sh` clones the pushed
branch fresh, runs `poe qa` (or the poe tasks you name after the branch) with
the worker cap and `nice -n 10`, deletes the directory, also on failure, and
passes the exit status through. Run it from the repository root:

```bash
ssh homelab 'bash -s -- <branch>' < python/scripts/homelab_qa.sh
```

The script copies a warm Lean build from
`~/.cache/substrait-lean/lake/<toolchain>` into the clone before building, and
replaces it with the clone's `.lake` after a successful run. Lake's trace
hashes rebuild whatever changed, so a cache from another commit is safe. It
keeps the caches of the two most recent toolchains, about 300 MB each.

The script refuses to start when less than 6 GB is available. It runs the
Lean build and the tests in two systemd user scopes, one after the other,
each with no swap. The tests' scope is capped at `HOMELAB_QA_MEMORY_MAX`
(8 GB), the build's at `HOMELAB_QA_BUILD_MEMORY_MAX` (the same by default).
`PYTEST_XDIST_AUTO_NUM_WORKERS`, `HOMELAB_QA_NICE`, `HOMELAB_QA_PREFIX` and
`HOMELAB_QA_CHECK_GENERATED` change the workers, the niceness of both
steps, the directory's prefix and whether the generated proofs are checked.
The first OOM kill stops its scope, which fails the run, and its directory
is deleted. A Lean change that sends `LiftDuckDB.lean`
into the full lift search once took 12.4 GB in one `lean` process and nearly
hung the box. Where user scopes are not available it
falls back to `ulimit -v`, which caps each process on its own. To stop a
run, send SIGTERM to the script's bash by its PID: it stops the running
scope and deletes the directory.

Run long QA commands there in the background, not in the foreground shell.

### Chaos suite

`python/tests/chaos/` injects crashes into pipeline execution: exceptions
and SIGKILLs at each step of a refresh, an S3 outage (moto behind a proxy),
sources that change or vanish, and racing writers. Its tests carry the
`chaos` marker, which only `-m chaos` selects, so `qa` and CI leave it out.
It spawns many processes, so run it on homelab, in the background and
capped, so that a QA run can go alongside it:

```bash
ssh homelab 'PYTEST_XDIST_AUTO_NUM_WORKERS=2 HOMELAB_QA_MEMORY_MAX=2G HOMELAB_QA_BUILD_MEMORY_MAX=8G HOMELAB_QA_NICE=19 HOMELAB_QA_CHECK_GENERATED=false HOMELAB_QA_PREFIX=substrait-chaos bash -s -- <branch> test-chaos' < python/scripts/homelab_qa.sh
```

Its Lean build skips the generated proofs (CI checks them on every PR) and
runs at the 8 GB cap: for those minutes it is as heavy as a QA run, so start
it under the same rules, with 6 GB available and a load under 8. Its tests
then run in their own scope at 2 GB, with 2 workers. One chaos run at a
time: check for a `/tmp/substrait-chaos-*` directory first. QA runs still
need 6 GB available.

Each scenario that fails appends a line to a JSONL ledger as it finishes
(`SVERIFY_CHAOS_LEDGER`, default `~/.cache/substrait-lean/chaos/<run>.jsonl`,
which outlives the run's directory; `tail -f` it). The task prints how
many scenarios ran and recovered, then the summary: failures grouped by signature, with counts and a
repro. `python -m sverify_dev.chaos summarize <ledger>...` summarises
partial or several ledgers (`--follow 60` repeats). Signatures with an
issue go in `tests/chaos/known.json`; their tests report as expected
failures, and a new signature fails the run. File issues per signature,
not per test.

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
  `sverify_dev.catalogue --write-tables`.

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

## Adding functions and coverage cases

Parallel PRs used to conflict in shared lists and dispatch tables; these are
now split by area. The areas are the same everywhere: `core` (logic,
comparisons, NULLs, arithmetic, math, bitwise), `strings` (with LIKE, regex,
digests), `temporal`, `nested` (lists, structs, lambdas, UNNEST),
`aggregates`, `windows`, `relations` and `casts`. A feature edits its area's
file; touch the shared `_base.py` only for what the area files say lives there.

- **Substrait function** (`SubstraitLean/Functions.lean`): add a row at the
  end of its area's table (`core`, `strings`, `temporal`, `nested`,
  `aggregates`, `windows`), one per constructor it is modelled by, with the
  next free anchor in that area's range (100s core, 200s strings, 300s
  temporal, 400s nested, 500s aggregates, 600s windows), its group from
  `docs/core-semantics.md`, its constructor and how the parser reads it.
  `Write.lean`'s anchors (`UnFn`/`BinFn`/`AggFn.anchor`, `fn "name"`) and
  `Pretty.lean` read the row. `lake build` rejects duplicate anchors or
  names, out-of-range anchors, a constructor with two rows and a group the
  design does not list. `substrait-check --functions` prints the tables as
  JSON for the Python mirror.
- **Coverage case** (`python/tools/sverify_dev/coverage_cases/<area>.py`): append to
  that module's `CASES`, and put its refusals in the same module's `REFUSED`,
  `TIE_FREE`, … (`coverage.py` documents them). A new area is a new module
  listed in `coverage_cases.AREAS`.
- **Parse** (`SubstraitLean/Parse.lean`): a row marked `reads := .plain`
  (`.float` for doubles) is read as its constructor with nothing more.
  Otherwise the function's arm in its area's `mkCoreCall?`, `mkStringCall?`,
  `mkTemporalCall?` or `mkNestedCall?`, before its last arm, which reads the
  table. Doubles go in `mkFloatCall`, decimals in `decimalCall`, constant folding in
  `foldCoreCall`/`foldTemporalCall`, aggregates in `parseMeasure`'s
  `match name, k`, windows in `parseWindow`'s `match baseName name, args`. A
  string function's integer arguments go in `stringFns`; an option's functions
  in that option's arm of `optionAccepts`.
- **Function table** (`python/src/sverify/_functions.py`, #544): a scalar
  function of strings, math or bitwise operations is a row: its anchor, area
  and group (`docs/core-semantics.md`), its kinds, the writer's operation, the
  SQL of each dialect, and the SQLGlot nodes and Ibis operations that read as
  it. A row whose `call`, `expr`, `lift` or `ibis` covers the function needs
  no case in the places below; `tests/test_functions.py` checks the rows
  against `Functions.lean` (`substrait-check --functions`).
- **SQL writer** (`python/src/sverify/sql/core/<area>.py`, `strings`,
  `temporal`, `nested`): the function's case in the area's `call` (`mkCall`),
  its SQL in the area's `expr`, and its result kind in the area's `UN_KINDS` or
  `BIN_KINDS`. In `_base.py`, add the op to the area's `<Area>UnOp`/`<Area>BinOp`
  Literal and the `Dialect` hook under the area's comment. Core functions,
  aggregates, windows, casts and relations are still in `_base.py`.
- **SQL lift** (`python/src/sverify/sql_lift/<area>.py`): the rule function and
  its entry in the area's `register({...})`, keyed by SQLGlot node type.
  Aggregates (`_AGGREGATES`), windows (`_RANKING`), joins, set operations and
  UNNEST are still in `_base.py`'s `_Lift`.
- **Ibis producer** (`python/src/sverify/ibis_substrait/<area>.py`): the rule
  and its entry in the area's `register({...})` (expressions),
  `register_rels({...})` (relations) or `register_refusals({...})`. Aggregates
  are a branch of `aggregates.measure`, window functions of `windows.window`;
  decimal typing (`_exact`) is in `_base.py`.
- **Tests of the lift**: `python/tests/test_sql_lift_<area>.py`, with the
  shared tables in `python/tests/_sql_lift.py`.
- **Black box** (#325), a DuckDB function the checker treats as opaque: add a
  row to `BlackBox.scalars` or `BlackBox.aggregates`
  (`SubstraitLean/BlackBox.lean`) with its types, NULL handling, whether it
  raises, its laws and a `sample` the laws allow (`scalars_wf` checks it by
  `decide`), and the same row, at the same index, to `TABLE` in
  `python/src/sverify/black_box.py` with DuckDB's SQL. Its anchor is 700 plus
  its index, under the black boxes' URN; the parser, the lift
  (`sql_lift/blackbox.py`), the writers and the refusals of other engines
  read the table, and `tests/test_black_box.py` checks the two tables agree.
  Add a lift rule only where SQLGlot reads the call as a node of its own
  (`to_base64`), and a Lean evaluator in `BlackBox.evalScalar` where Lean can
  compute it exactly. Test it in `tests/test_black_box.py`: oracle C, the
  laws on random data, a contract they prove. A new law kind needs its case
  in `BlackBox.Law.holds` and `Law.bound` (`Contracts.lean`).
- **Engine support** (`python/src/sverify/_support.py`): a function that not
  every engine runs (a new one runs on DuckDB only, #271) gets a row in
  `SUPPORT` with the engines that run it. `to_sql` and `run_plan` refuse it
  on the others before they dispatch, with "see #271". Refusals that depend
  on types or arguments stay in the engine.
- **Reference semantics** (`docs/reference-semantics.md`): the area's section.

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

## Engine facts

What an engine does (overflow, NaN, casts, the algorithm behind `VARIANCE`, …)
is recorded as facts, one JSON document per finding:
`characterization/<engine>/facts/<id>.json` (`duckdb/`, `polars/`, `spark/`,
…), in the format of `characterization/fact.schema.json`. Every engine's
research goes there, whoever does it.

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
  release tag: DuckDB's sqllogictests, Polars's unit tests; method
  `engine-test`, or `replay` through `sverify_dev.slt`) < `probe` (probes,
  repros) < `fuzz` < `proof`. Research goes in that
  order, the cheaper kinds first.
- `rows` names the rows of the engine choice tables the fact settles: a
  function group of `Functions.lean`, one of its options, and only the types
  its checks covered. `python -m sverify_dev.facts --coverage <engine>` lists
  each row's facts, or `missing`, then the checklist's areas as a rollup.
- A new check of an old fact adds to its `provenance`. A fact that no longer
  holds (a new engine version) gets a new document with `supersedes`, and the
  old one `superseded_by`.

`python -m sverify_dev.facts` checks the documents (`tests/test_facts.py`
does too). The JSON documents are the record: there is no generated overview. The judging principles and the
DuckDB diff table are in `characterization/duckdb/README.md`.

## Upstream bugs

When you find a bug in SQLGlot, an engine, Ibis or Substrait's tooling, add
a document `upstream/bugs/<id>.json` in the same PR as the workaround, in the
format of `upstream/bug.schema.json`: the version, a status, a minimal
reproduction, how sverify handles it, and what it was last checked against
(`checked`). The id is the project's prefix and the next free number (`SG-8`,
`DD-5`; `upstream/README.md` lists the prefixes); the file is named after it.
Link the files of the workaround (`files`) and the engine facts that record
it (`facts`). We file them upstream in batches, with the `upstream-report`
skill. Documented engine behaviour that only differs from the reference model
goes into the engine's characterization.

Behaviour the Substrait YAMLs leave unspecified, but that Substrait could
express (a missing option, option value or default), is a spec gap: add an
`ST-<n>` document with `kind: spec-gap` in the same PR that meets it, saying
how Substrait could express it and what each engine does (its facts).
`docs/core-semantics.md` lists the ones found so far.

`python -m sverify_dev.bugs` checks the documents and the lift's backlog
`python/tests/lift_backlog.json` (`tests/test_bugs.py` does too).

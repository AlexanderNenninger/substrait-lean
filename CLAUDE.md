# Notes for Claude

## Running QA

`poe qa` (from `python/`) runs everything: Lean proofs, build, lint,
typecheck, golden tests and the Python tests. It is slow on this laptop.

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

Run one expensive task at a time per agent, never several in parallel. The
poe test tasks use `pytest -n auto`, which takes every core. On the laptop,
run pytest directly with `-n 2` instead.

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
  locally.
- **Don't start** if the 1-minute load average is above 8, or if less than
  6 GB is available (the `available` column of `free -g`).
- **Cap the workers:** the poe test tasks use `pytest -n auto`, which takes
  every core. Set `PYTEST_XDIST_AUTO_NUM_WORKERS=6` so a run leaves half the
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

Run long QA commands there in the background, not in the foreground shell.

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

Generated Lean modules are different: `SubstraitLean/LoweringDuckDB/Off` and `On`
(the DuckDB lowering) and `SubstraitLean/LiftDuckDB/Duckdb` and `Reference` (the
lift from DuckDB SQL), entries with their proofs, are committed, and a build only
checks them. When a build fails there, or a golden test of theirs changes,
regenerate them with `poe regen-lowering` or `poe regen-lift` and commit the
result. Both cap Lean at 6 GB (`-M 6144`).

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

- **Substrait function** (`SubstraitLean/Write.lean`): add `(anchor, name)` at
  the end of its area's list (`coreFns`, `stringFns`, `temporalFns`,
  `nestedFns`, `aggregateFns`, `windowFns`) with the next free anchor in that
  area's range (100s core, 200s strings, 300s temporal, 400s nested, 500s
  aggregates, 600s windows), and the matching arm in `UnFn`/`BinFn`/`AggFn.anchor`
  under the area's comment. `lake build` rejects duplicate anchors or names,
  out-of-range anchors and anchors that are not declared.
- **Coverage case** (`python/tools/sverify_dev/coverage_cases/<area>.py`): append to
  that module's `CASES`, and put its refusals in the same module's `REFUSED`,
  `TIE_FREE`, … (`coverage.py` documents them). A new area is a new module
  listed in `coverage_cases.AREAS`.
- **Parse** (`SubstraitLean/Parse.lean`): the function's arm in its area's
  `mkCoreCall?`, `mkStringCall?`, `mkTemporalCall?` or `mkNestedCall?`, before
  its `| _, _ => none` (core: before the trailing `BitOp` arm too). Doubles go
  in `mkFloatCall`, decimals in `decimalCall`, constant folding in
  `foldCoreCall`/`foldTemporalCall`, aggregates in `parseMeasure`'s
  `match name, k`, windows in `parseWindow`'s `match baseName name, args`. A
  string function's integer arguments go in `stringFns`; an option's functions
  in that option's arm of `optionAccepts`.
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

## Upstream bugs

When you find a bug in SQLGlot, an engine, Ibis or Substrait's tooling, add
an entry to `upstream/LEDGER.md` in the same PR as the workaround: the
version, a minimal reproduction, and how sverify handles it. We file them
upstream in batches. Documented engine behaviour that only differs from the
reference model goes into the engine's characterization, not the ledger.

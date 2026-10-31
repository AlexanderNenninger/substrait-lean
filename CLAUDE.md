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

Several agents share the box, so check its load before starting a run:

```bash
ssh homelab 'nproc; uptime; ls -d /tmp/substrait-lean-* 2>/dev/null | wc -l'
```

If the 1-minute load average is above 8, or two QA runs are already going
(two `/tmp/substrait-lean-*` directories), don't add another: wait a few
minutes and check again, or run only the tests your change touches locally.
Run QA under `nice -n 10` so interactive use of the box stays responsive.

Each run gets its own directory,
`/tmp/substrait-lean-<uuid>`. Never run tests in a shared checkout such as
`~/Projects/substrait-lean`. Clone the branch fresh and delete the directory
afterwards:

```bash
ssh homelab 'export PATH=$HOME/.elan/bin:$HOME/.local/bin:$PATH
  dir=/tmp/substrait-lean-$(uuidgen)
  git clone -q --branch <branch> https://github.com/AlexanderNenninger/substrait-lean.git "$dir"
  cd "$dir/python" && nice -n 10 uv run poe qa; status=$?
  rm -rf "$dir"; exit $status'
```

Run long QA commands there in the background, not in the foreground shell.

## Generated files

Don't commit regenerated tables on a feature branch. They are rewritten on
`main` after every merge by the `Generated files` workflow
(`.github/workflows/generated.yml`), so committing them only causes merge
conflicts with other PRs:

- `README.md`'s coverage table (`<!-- coverage:start -->` … `<!-- coverage:end -->`),
  from `sverify.coverage --write-readme`;
- `catalogue/INDEX.md` and `catalogue/FINDINGS.md`'s stats tables, from
  `sverify.catalogue --write-tables`.

If you ran one of these commands locally, `git checkout` those files again
before you commit. Edit the sources instead: the `CASES` of
`python/src/sverify/coverage_cases/<area>.py`, the catalogue's TOML, and
`catalogue/status.json`. `status.json` is not just output: it holds the results
`tests/test_catalogue.py` expects. So a PR that adds a catalogue query or
changes coverage commits it, after `sverify.catalogue --write`.

## Adding functions and coverage cases

Parallel PRs used to conflict in two shared lists; both are now split by area.

- **Substrait function** (`SubstraitLean/Write.lean`): add `(anchor, name)` at
  the end of its area's list (`coreFns`, `stringFns`, `temporalFns`,
  `nestedFns`, `aggregateFns`, `windowFns`) with the next free anchor in that
  area's range (100s core, 200s strings, 300s temporal, 400s nested, 500s
  aggregates, 600s windows), and the matching arm in `UnFn`/`BinFn`/`AggFn.anchor`
  under the area's comment. `lake build` rejects duplicate anchors or names,
  out-of-range anchors and anchors that are not declared.
- **Coverage case** (`python/src/sverify/coverage_cases/<area>.py`): append to
  that module's `CASES`, and put its refusals in the same module's `REFUSED`,
  `TIE_FREE`, … (`coverage.py` documents them). A new area is a new module
  listed in `coverage_cases.AREAS`.

## Notebook voice

The tour's markdown cells (`notebooks/`) are written for a data engineer with
a stake in the outcome. Keep this voice when you edit them:

- **Openings are a short story** of two or three sentences, in the second
  person, that set the scene and the stakes. Then the rule or feature.
- **Name the people a result affects** (the customer, whoever gets paged at
  3 a.m., the analyst reading the dashboard), and state requirements as what
  those people rely on.
- **Walkthrough steps say "we"**: "We'll write the rule in Ibis, state what it
  assumes and what it promises, and have the checker prove it before any
  data runs." Openings and recaps speak to the reader as "you".
- **Technical explanations are plain and warm, with no humour.** For example:
  "In SQL, `NaN > 30` is TRUE: NaN sorts above every number, so a glitching
  sensor that sends NaN counts as hot and pages someone. We'll want to rule
  that out." Humour, aimed at the data rather than the reader (bad rows can
  be characters), belongs only in openings and asides, at most once per cell.
- **Endings are a warm recap, not a bullet list**: a short paragraph to the
  reader about what they can now do, leading into the next notebook, with
  its link.
- Keep every fact, identifier, link and number. Don't soften technical
  claims or hide caveats: the warmth goes in the framing, not the substance.
- Stay concise: at most about a third longer than plain prose would be. No
  emojis or exclamation marks, and no "simply" or "just".

An opening: "Say you're on the payments team. A customer was charged twice for
the same coffee, and by the time support hears about it, they've already
tweeted. You want to catch these double charges, the same card paying the
same amount at the same merchant twice within five minutes, and refund them
first."

An ending: "You now have a refund queue you can trust. Its assumptions were
proved before a single row ran, it stays right as charges arrive and get
reversed, and the next job can build on it without checking again. Next up:
sensor alerts, where ties and NaN get involved."

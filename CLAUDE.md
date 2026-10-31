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
before you commit. Edit the sources instead: `CASES` in
`python/src/sverify/coverage.py`, the catalogue's TOML, and
`catalogue/status.json`. `status.json` is not just output: it holds the results
`tests/test_catalogue.py` expects. So a PR that adds a catalogue query or
changes coverage commits it, after `sverify.catalogue --write`.

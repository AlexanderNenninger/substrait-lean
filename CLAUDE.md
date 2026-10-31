# Notes for Claude

## Running QA

`poe qa` (from `python/`) runs everything: Lean proofs, build, lint,
typecheck, golden tests and the Python tests. It is slow on this laptop.

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

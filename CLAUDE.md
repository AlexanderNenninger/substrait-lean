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

Several agents may run QA at once, so each run gets its own directory,
`/tmp/substrait-lean-<uuid>`. Never run tests in a shared checkout such as
`~/Projects/substrait-lean`. Clone the branch fresh and delete the directory
afterwards:

```bash
ssh homelab 'export PATH=$HOME/.elan/bin:$HOME/.local/bin:$PATH
  dir=/tmp/substrait-lean-$(uuidgen)
  git clone -q --branch <branch> https://github.com/AlexanderNenninger/substrait-lean.git "$dir"
  cd "$dir/python" && uv run poe qa; status=$?
  rm -rf "$dir"; exit $status'
```

Run long QA commands there in the background, not in the foreground shell.

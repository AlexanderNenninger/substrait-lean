---
name: chaos-run
description: Run the chaos suite (python/tests/chaos/, crash injection into pipeline refreshes) on homelab and read its ledger: the command, capacity rules, the JSONL ledger, summarize, known.json. Use when testing crash recovery, S3 outages or racing writers, or when asked to run chaos.
---

# Chaos suite

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

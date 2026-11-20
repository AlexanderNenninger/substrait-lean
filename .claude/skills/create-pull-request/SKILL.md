---
name: create-pull-request
description: Open a pull request for sverify: branch, the cheap checks before the push, the body (Fixes #N or Part of #N, the Improvement lines, the changelog fragment), one push, the reviewer, and how the mergeq service merges it. Use whenever you are about to push a branch and open a PR, or push again to a PR that is open.
---

# Create a pull request

A PR goes from a branch off `main` to `main`, is reviewed, carries the
`reviewed` label, and the mergeq service merges it in a batch once its `qa`
check is green. Nobody merges by hand.

## 1. Branch

- Branch off a fresh `origin/main` (`git fetch origin main`), never off another
  PR's branch: a PR into a branch other than main runs `static` only and its `qa`
  fails (`.github/workflows/retarget.yml`).
- Stay in your task's files. A file outside them that needs changing goes to
  the coordinator, since another session may own it.
- Before a new Lean module or a new name, check it is free (`git ls-files`,
  `git grep`).

## 2. Checks before the push

From `python/`, with the venv's tools:

```bash
.venv/bin/poe fmt
.venv/bin/poe lint
.venv/bin/poe typecheck
```

Never use a plain `uv run`: after a `pyproject.toml` or `uv.lock` change it rebuilds the package, and the build hook starts a full `lake build` outside the capacity slots. poe runs its tasks with `uv run --no-sync`.

- **Lean changes:** build with `lake build --wfail` through the drivers
  (`local-run --slots 2`) or on homelab, never bare on the laptop.
- **Tests:** run the tests of the files you changed through `local-run`, one slot. The full suite runs in CI.
- **Resolved conflicts:** after a merge with conflicts, run the tests of every file you resolved, not only your own change's.

## 3. The body

- **Issues:** `Fixes #N` for each issue the PR completes, so GitHub closes it at the merge. A PR that does part of an issue says `Part of #N`, and you comment on the issue what remains, so the issue still reads true. Never `Fixes` an issue whose acceptance isn't fully met.
- **What and why:** in plain words. Name the decision (D-number) or ruling a semantic change rests on. User docs carry no D-numbers.
- **Improvement:** one line for performance and one for code quality, each with a number before and after (CLAUDE.md, "Every PR leaves its area faster and simpler"). A PR with nothing measurable says so.
- **Not verified:** what you did not run, such as engines, homelab or the full suite.
- **Changelog:** a change a user notices adds one file to `changelog.d/` (its README). Never edit `CHANGELOG.md`.
- **Generated files:** generated tables (README coverage, catalogue stats, realizability, `upstream/REPORT.md`) are not committed on a feature branch. Generated Lean modules are committed after `poe regen-*`.
- **Closing line:** end with the attribution line the session's instructions give.

## 4. Push and open

- **Push once:** push finished work in one push. Every push queues a full CI run, and the repository has 20 runner slots.
- **Open as ready:** open the PR ready for review, not as a draft (`gh pr create --base main`).
- **Main merges:** merge `main` into the branch only when it conflicts, when mergeq refuses it as stale (base older than 6 h), or when the coordinator asks.

## 5. Review and merge

- **Reviewer:** send the PR to the reviewer of its area, and tell the coordinator.
  - Reviewer 1 takes implementation and Lean.
  - Reviewer 2 takes Python, CI, docs and coverage.
  - Reviewer 3 takes docs, tests and CI.
- **The label:** the reviewer adds `reviewed`. mergeq admits the PR once `qa` is green at its head and its base is under 6 h old, swaps the label for `queued`, batches it with others and bisects a failed batch.
- **Pushes after approval:** a push after the approval is let back in on green `qa` without a new review. After a substantive push, tell the reviewer, who removes the label until they have looked. A clean merge of `main` needs nothing.
- **Cancelled runs:** a red `qa` whose other jobs were cancelled means a batch is testing the PR. Don't rerun it or "fix" it.

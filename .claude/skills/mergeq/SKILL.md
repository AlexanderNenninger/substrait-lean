---
name: mergeq
description: Get a reviewed pull request merged through the mergeq service, the batch merge queue for main. Covers the labels (`reviewed`, `queued`, `mergeq-dropped`, `mergeq-paused`), the admission rules, reading the queue's status, what each refusal means and fixes, batches and bisection, closing issues by hand, and the cases mergeq doesn't handle (release branches, a stale main). Use when labelling a PR, when a PR is refused or dropped, when a batch fails, when the mergeq bot comments on a PR, or when asked why a PR hasn't merged.
---

# Merging through mergeq

Main takes changes through the mergeq service, the batch merge queue running on homelab (its own repository, `~/Projects/homelab`). Nobody merges a PR into main by hand. Opening and pushing a PR is the `create-pull-request` skill. This skill picks up once the PR is reviewed.

## How a PR gets merged

1. A reviewer approves the PR and adds the `reviewed` label.
2. mergeq admits the PR when both hold:
   - its own `qa` check is green at the PR's head;
   - its base, the main commit it was last merged with, is under 6 hours old (`admission.max_base_age`).
3. On admission mergeq swaps `reviewed` for `queued`, collects queued PRs into a batch branch `batch/<date>-<time>-<numbers>`, and opens a batch PR whose CI tests them together.
4. The batch's CI runs everything. The PRs' own runs are cancelled while it does, and the bot says so in a comment.
5. On green, mergeq merges the batch PR into main as a merge commit, which carries each member's merge.
6. On red, it bisects: it splits the batch, retests the halves, and drops the member that fails, labelling it `mergeq-dropped` with a comment naming the failure.

## Reading the queue

```bash
curl -s https://mergeq.tailf11061.ts.net/api/repos/AlexanderNenninger/substrait-lean/queue
```

The JSON has these keys:
- `queued`: admitted, waiting for the next batch;
- `batch`: the running batch, with its number, members and `created_at`;
- `bisection`: a failed batch being split;
- `refused`: labelled but not admitted, each with a `reason`;
- `held`, `decisions` and `restarts`: the service's log;
- `paused` and `pause`: a pause set by the maintainer (the `mergeq-paused` label).

Read it before acting on a PR that hasn't merged. A batch running for more than an hour is stuck, so tell the coordinator.

## Refusals and what fixes them

| Reason in `refused` | Fix |
| --- | --- |
| `its own qa failed at <sha>` | A real failure. Read the failing job (`gh pr checks`), fix it, push once. |
| `its required checks haven't all passed at <sha>` | CI is still running. Wait; mergeq retries on its own. |
| `its branch is based on main as of N h ago, more than the 6.0 h ...` | Merge main into the branch and push once. The label stays, and the new head's green `qa` readmits it. |
| `conflicts with main` | Merge main and resolve. Then run the tests of every file you resolved, since a resolution can drop the other side's code. Push once. |

A PR with `mergeq-dropped` failed in a batch. Read the bot's comment and the batch's failing job. If the failure is the PR's own, fix it, push and ask the reviewer to relabel. If the failure came from another member, or from a clash with one (two PRs re-recording `route_pins.json` or the census, say), merge main after the other lands, re-record and push.

## Labels after a push

- A clean merge of main needs no re-review. The label stays.
- A substantive push after approval: the reviewer removes `reviewed` and `queued`, reviews the new head, and relabels. The author tells the reviewer.
- Never relabel your own PR.

## Things not to do

- Don't rerun a cancelled `qa`. A red `qa` whose other jobs show `cancelled` means a batch is testing the PR. Check the queue and the PR's state first (`gh run view <id> --json jobs`).
- Don't merge main after every push. Each push restarts the whole CI run, and the repository runs at most 20 jobs at once.
- Don't push to a branch while its PR is in a running batch unless the batch failed on it.
- Don't merge into main by hand. The coordinator is the one exception, below.

## Closing issues

When a batch merges, GitHub doesn't close the issues a member's `Fixes #N` names. After a member merges, the coordinator closes each issue it fixes by hand, after checking the PR completed it. A PR that only does part of an issue says "Part of #N", and the issue stays open with a comment saying what's left. (homelab PR #162 makes mergeq close them itself; until it merges, closing is by hand.)

## What mergeq doesn't handle

- Release branches. A PR into `release/<major>.<minor>` isn't queued. The coordinator merges it by hand once it's reviewed and green (the `release-sverify` skill), as a merge commit.
- A stale main. The 6-hour base rule measures the age of main's head. If nothing has merged for six hours, because a repository-wide CI failure blocks every PR, merging main can't satisfy the rule. The coordinator then merges the PR that unblocks CI by hand, once it's reviewed and its checks are green, and the queue moves again. That happened with #2609 on 2026-11-26, when a new Polars release broke the `no-duckdb` job.
- A paused queue. While `mergeq-paused` is set, nothing is batched. Only the maintainer lifts it.

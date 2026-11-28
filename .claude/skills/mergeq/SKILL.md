---
name: mergeq
description: Get a reviewed pull request merged through the mergeq service, the batch merge queue for main. Covers the labels (`reviewed`, `queued`, `mergeq-dropped`, `queue-first`, `queue-alone`, `do-not-merge`, `do-not-batch`, `mergeq-paused`, and `on-hold`, which mergeq doesn't read), the admission gate, reading the queue's status, what each refusal means and fixes, batches, rebuilds, serial bisection and the repo-wide pause, closing issues by hand, and the cases mergeq doesn't handle. Use when labelling a PR, when a PR is refused, dropped or not batched, when a batch fails or the queue pauses, when the mergeq bot comments on a PR, or when asked why a PR hasn't merged.
---

# Merging through mergeq

Main takes changes through the mergeq service, the batch merge queue running on homelab. Its full description, including the address of its status page and API (Tailscale only), is `mergeq/README.md` in the homelab repository (`~/Projects/homelab`). This repository's settings are in `.github/mergeq.yml`. Nobody merges a PR into main by hand. Opening and pushing a PR is the `create-pull-request` skill; this skill picks up once the PR is reviewed.

## Reviews and the label

Every session posts as the same GitHub account, and GitHub won't let an account approve its own PR. So a review goes up as a comment (`gh pr review --comment` or `gh pr comment`), and the `reviewed` label is the approval mergeq reads. Never label your own PR.

| Label | Set by | Meaning |
| --- | --- | --- |
| `reviewed` | a reviewer | Ready. mergeq admits the PR once the gate below passes, and swaps the label for `queued`. |
| `queued` | mergeq | In the queue, the running batch or a bisection. |
| `mergeq-dropped` | mergeq, with a comment | A bisection found it failing on the base, or its push was refused. Out of the queue until it's fixed and labelled `reviewed` again. |
| `queue-first` | the coordinator | Ahead of every other queued PR. |
| `queue-alone` | the coordinator | Tested and merged in a batch of its own. |
| `do-not-merge` | anyone | Held: never admitted, and a queued PR that gets it leaves the next batch. Use it to hold a PR. |
| `do-not-batch` | anyone | The same as `do-not-merge` today: mergeq reads both as one hold. |
| `mergeq-paused` | mergeq, on an issue | The queue is paused after a repo-wide failure: nothing is batched or merged while the issue is open (below). |

`on-hold` is not read by mergeq, so it holds nothing: a PR with `on-hold` and `reviewed` is admitted. Hold a PR with `do-not-merge`.

mergeq's labels are in its code (`mergeq/src/mergeq/queue.py` in the homelab repository); `.github/mergeq.yml` names only `ready_label`.

## The admission gate

mergeq admits a `reviewed` PR when all of these hold:
- every required check (`qa` here) concluded `success` at the PR's current head. Pending isn't enough;
- its merge base with main is at most 6 hours old (`admission.max_base_age`);
- it isn't a draft;
- GitHub reports it mergeable.

A push to a queued PR sends it back to `reviewed` until the new head is green, then it's queued again. A push after review needs no re-review, so after a substantive push the reviewer removes `reviewed` and `queued` themselves and relabels after looking. A clean merge of main needs nothing.

## How a batch runs

1. Once enough PRs are queued, or the oldest has waited long enough, mergeq merges their heads onto main in a branch `batch/<stamp>-<members>` and opens a batch PR. It comments on each member and cancels the members' own runs, since the batch tests them.
2. A member that conflicts at build time stays `queued`, with a comment, and is left out.
3. Green, and main hasn't moved: mergeq merges the batch with a merge commit, which marks every member merged. If main moved, or a member was pushed to while the batch ran, it closes the batch and builds it again on the new base.
4. Red: one PR alone is dropped. Several are bisected serially: the first half is tested on the current base. A green half merges, and its sibling is then the suspect; a red half is split again. One culprit in eight costs three runs. A PR dropped after a half merged may only clash with that half (two PRs re-recording `route_pins.json` or the census, say); the drop comment names the pair.
5. Repo-wide failure: if every failed job also fails on main, or in at least two other PRs' own runs within 3 hours, bisecting would only drop innocent PRs. mergeq then closes the batch, drops nothing, keeps the PRs queued and pauses itself. The pause is an open issue labelled `mergeq-paused`. Fix the failure first; the operator (the maintainer) resumes the queue, and closing the issue by hand also resumes it.

## Reading the queue

The status API (address in the homelab README) returns JSON with:
- `ok`, `error`: whether the last tick worked, and why not;
- `paused`, `pause`: a pause and its reason;
- `queued`: admitted PRs waiting for the next batch;
- `batch`: the running batch, its number, members and `created_at`;
- `bisection`: a bisection in progress;
- `refused`: labelled PRs the gate turned away, each with a `kind` and a `reason`, and `refused_by_reason` counting them;
- `waiting_on`: what the queue is waiting for;
- `held`, `decisions`, `restarts`: the service's recent actions.

Read it before acting on a PR that hasn't merged. A batch running for more than an hour may be stuck; tell the coordinator.

## Refusals and what fixes them

| Reason | Fix |
| --- | --- |
| `its own qa failed at <sha>` | A real failure. Read the failing job (`gh pr checks`), fix it, push once. |
| `its required checks haven't all passed at <sha>` | CI is still running. Wait; mergeq retries every minute. |
| `its branch is based on main as of N h ago, more than the 6.0 h ...` | Merge main into the branch and push once. The label stays, and the new head's green `qa` admits it. |
| `conflicts with main` | Merge main and resolve, then run the tests of every file you resolved, since a resolution can drop the other side's code. Push once. |
| mergeability unknown | GitHub hasn't computed it yet. Wait a tick. |
| (not listed at all) | The PR is a draft, carries `do-not-merge` or `do-not-batch`, or lacks `reviewed`. |

## Things not to do

- Don't rerun a cancelled `qa`. `qa` is an aggregate job, so a cancelled run shows `qa` as `failure`. A red `qa` whose other jobs show `cancelled` means a batch is testing the PR; mergeq itself treats a cancelled check as not run. Check the queue and the PR's state first (`gh run view <id> --json jobs`).
- Don't merge main after every push. Each push restarts the whole CI run, and the repository runs at most 20 jobs at once.
- Don't push to a branch while its PR is in a running batch unless the batch failed on it.
- Don't merge into main by hand. The coordinator is the one exception, below.

## Closing issues

When a batch merges, GitHub doesn't close the issues a member's `Fixes #N` names. After a member merges, the coordinator closes each issue it fixes by hand, after checking the PR completed it. A PR that does only part of an issue says "Part of #N", and the issue stays open with a comment saying what's left. Homelab PR #162 makes mergeq close them itself; until it merges, closing is by hand.

## What mergeq doesn't handle

- Release branches. A PR into `release/<major>.<minor>` isn't queued. The coordinator merges it by hand once it's reviewed and green (the `release-sverify` skill), as a merge commit.
- A stale main. The 6-hour rule measures the merge base's age. If nothing has merged for six hours, because a repository-wide CI failure blocks every PR, merging main can't satisfy it. The coordinator then merges the PR that fixes CI by hand, once it's reviewed and its checks are green, and the queue moves again. That happened with #2609 on 2026-11-26, after a new Polars release broke the `no-duckdb` job.
- A paused queue. While the `mergeq-paused` issue is open, nothing is batched or merged. Only the maintainer resumes it.

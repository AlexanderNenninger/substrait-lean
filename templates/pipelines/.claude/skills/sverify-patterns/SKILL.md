---
name: sverify-patterns
description: >
  Write common data engineering patterns with sverify and the contract that
  makes each worth proving: deduplicate or keep the latest row per key,
  sessionize events (gaps and islands), double-entry bookkeeping and ledger
  reconciliation (full outer join), funnels, cohorts and retention, floating
  point aggregates across engines, SCD type 1, 2 and 4 over a change feed,
  running balance and FIFO profit and loss, time-weighted averages and counter
  resets, gap filling (last observation carried forward). Use when a user
  names one of these patterns or asks how to write it so the guarantees are
  proved.
---

# sverify patterns: the rule and its contract

Each pattern is a reference file with the rule in Ibis and in SQL, the contract
that verifies on the current release, the refusals and suggestions sverify
gives it, and what stays unproved. Read the `sverify` skill first for the API
and `sverify-pipelines` for sources, sinks and refresh.

| The user wants to | Reference |
|---|---|
| keep one row per key, the latest | `references/dedup.md` |
| split events into sessions, find runs | `references/sessionize.md` |
| reconcile two systems, post double entries | `references/reconcile.md` |
| count users by step, cohort or week | `references/funnel.md` |
| add doubles and get the same answer on every engine | `references/float-aggregates.md` |
| keep the history of a changing row | `references/scd.md` |
| a running balance, matched lots (FIFO) | `references/running-balance.md` |
| rates from a counter, a time-weighted mean | `references/counters.md` |
| carry the last value forward over gaps | `references/gap-filling.md` |

## The recipe

1. Write the rule as an Ibis expression (or `sv.sql("...", t=table)`).
2. State what the inputs guarantee in `requires` (keys, NOT NULL, ranges, a
   row cap). Take only what the source keeps.
3. State what consumers rely on in `ensures`: a key, NOT NULL, a range.
4. Run `sv.verify` (or `sverify check pipelines/<file>.py --json`). Read the
   report: `needs` and `report.suggested_requires` name the bounds a proof
   uses, `unproved` comes with a counterexample, `issues` lists runtime errors.
   `sverify check --fix` adds the needed preconditions to `requires=`.
5. Repeat until the report says proved, then run the node.

## What the lenses prove and what they don't

- A window function's value is nullable to the proof and has no upper bound.
  State a lower bound as `_.x.isnull() | (_.x >= 0)`, and bound a window total in
  `requires` of the node that reads it.
- A comparison of two columns does not narrow a branch: `CASE WHEN c >= prev
  THEN c - prev ELSE c END` is bounded, and its sign is unproved.
- A key survives a window and a filter. It does not survive a full outer join
  that computes the key with `coalesce`: keep it out of `ensures` there.
- Rows that tie in a window's `ORDER BY` give the engine a choice. Declare a
  key that includes the order columns (`sv.unique("id", "ts")`) for a
  reproducible result.

## A new pipeline from scratch

1. Ask only what the data cannot say.
2. Probe the source: a few hundred rows, their types, keys, NULLs and ranges.
3. Write the source, the transform with its contract and the sink.
4. Loop with `sverify check --json` and `--fix` until the contract proves.
5. State the contract in plain words and ask once.
6. Refresh, and schedule the refresh.

Eurostat republishes whole datasets with revisions: a snapshot source with the
key `(geo, unit, na_item, time)`, `:` for missing values and a flag column. Keep
the latest revision per key (`references/dedup.md`) and its history when the
revisions matter (`references/scd.md`).

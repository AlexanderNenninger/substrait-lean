# `Refresh.monotone`

A node's commits under one plan only move forward: no state is committed twice
in a row, and none goes back.

Lean: `Substrait.Refresh.monotone`, in
[`analysis/Sverify/Analysis/Refresh.lean`](../../analysis/Sverify/Analysis/Refresh.lean).
Twin for a source that cannot restore: `RefreshSnap.monotone`, in
[`RefreshSnapshot.lean`](../../analysis/Sverify/Analysis/RefreshSnapshot.lean).
Layer: the refresh protocol as a transition system. Axioms: `propext`,
`Quot.sound` ([trusted-base.md](../trusted-base.md)).

## What it says

Look at two adjacent commits of the node in a sink's log, of one plan. The
later one is of a later version of the source (durable source), or of a version
not below the earlier one and of other contents (a source that cannot restore,
which numbers its reads per process). So no two adjacent commits of the node
under one plan are of the same state. A commit right after another
application's rows may write the same state again: it repairs the table, so
only adjacent commits of the node count.

## The statement, line by line

```lean
theorem Refresh.monotone {s : World} (h : Reachable s) : AdjOK s.log
```

- `s`, `h`: a reachable state.
- `AdjOK s.log`: for every two adjacent commits `c'` (later) and `c` (earlier)
  of the node under one plan, `c.key.ver < c'.key.ver`.

## What it rules out

- The same state committed twice in a row by the node under one plan.

## What it does not cover

- Liveness. A refresh may never happen; the theorem orders the commits that do.
- A plan change: it starts a new run of commits, and the theorem says nothing
  across plans.
- That a refresh whose source has not changed commits nothing
  (`Refresh.next_unchanged`), and that a restarted process resumes and does not
  rewrite in full (`Refresh.no_needless_rewrite`, #889): these are lemmas of
  their own about `next`.
- Two plans alive at once (a rolling deploy) replace each other's state on
  every refresh until the old one stops; the states are right and the log grows
  by one full copy per refresh meanwhile.

## Its side conditions

Reachability only.

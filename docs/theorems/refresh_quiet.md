# `Refresh.quiet`

Once the environment is quiet, the refresh steps reach the deployed plan's
state of the source, and keep it.

Lean: `Substrait.Refresh.quiet`, in
[`analysis/Sverify/Analysis/Refresh.lean`](../../analysis/Sverify/Analysis/Refresh.lean).
Twin for a source that cannot restore: `RefreshSnap.quiet`, in
[`RefreshSnapshot.lean`](../../analysis/Sverify/Analysis/RefreshSnapshot.lean).
Layer: the refresh protocol as a transition system. Axioms: `propext`,
`Classical.choice`, `Quot.sound` ([trusted-base.md](../trusted-base.md)).

## What it says

Take any reachable state in which no write of a crashed process is in flight.
Suppose then that no source changes, no plan is deployed, no other
application writes the sink, and no process crashes or loses an
acknowledgement: only the processes' own steps (start, stop, refresh, prepare,
land, conflict) happen. Then a finite run of those steps brings the sink's
table to the plan deployed now, on the source as it is, and no further
process step changes it. This is the safety half of convergence.

## The statement, line by line

```lean
theorem Refresh.quiet {s : World} (h : Reachable s) (hz : s.zombies = []) :
    ∃ t, PReach s t ∧ ∀ t', PReach t t' → t'.tbl = .rows s.deployed s.src
```

- `s`, `h`, `hz`: a reachable state with no write of a crashed process in
  flight.
- `PReach s t`: `t` follows `s` by finitely many steps of the processes
  themselves.
- The conclusion: some such `t` has the property that every state reachable
  from it by process steps has the table of the deployed plan on the source's
  current version.

## What it rules out

- A protocol that can stall in a wrong state with nobody to move it: old-plan
  processes finish and stop, one fresh process commits the right state, and
  the others skip.

## What it does not cover

- Fairness. That the processes take these steps at all is an assumption and
  not proved; the [chaos suite](../../python/tests/chaos/) exercises it by
  killing and restarting writers and checking the sink converges.
- The environment's own steps. A late write of a crashed process, a foreign
  commit or a deploy during the run is outside the theorem.

## Its side conditions

Reachability and no crashed process's write in flight.

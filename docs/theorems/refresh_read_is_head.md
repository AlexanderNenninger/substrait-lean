# `Refresh.read_is_head`

A change that lands on a sink lands on the commit it was computed from.

Lean: `Substrait.Refresh.read_is_head`, in
[`analysis/Sverify/Analysis/Refresh.lean`](../../analysis/Sverify/Analysis/Refresh.lean).
Twin for a source that cannot restore: `RefreshSnap.read_is_head`, in
[`RefreshSnapshot.lean`](../../analysis/Sverify/Analysis/RefreshSnapshot.lean).
Layer: the refresh protocol of one stored node as a transition system:
the theorem speaks of `Reachable` states. Axioms: `propext`, `Quot.sound`
([trusted-base.md](../trusted-base.md)).

## What it says

A write in flight remembers how long the sink's log was when it read the
node's record. While the log still has that length, nothing was committed
since, so the write sees the log it read. If the write is a change, the
newest commit of the log is the node's, it is the sink's record, and the
table is the state the change was computed from. A commit that does not
find the log as it read it is refused (`conflict`), which is the
compare-and-swap of Delta and Iceberg.

## The statement, line by line

```lean
theorem Refresh.read_is_head {s : World} {o : Out} (h : Reachable s)
    (hp : Pending s o) (hm : o.mode = .merge) (hc : s.log.length = o.head) :
    kept s.log = true ∧ ∃ r, record s.log = some r ∧ o.base = r.tbl
```

- `s`, `h`: a reachable state of the protocol.
- `o`, `hp`: a write in flight in it, a process's or a crashed process's
  (`Pending`).
- `hm`: the write is a change on a table (`merge`), as against a full
  replacement.
- `hc`: the log has the length the write read.
- The conclusion: no other application wrote since the node's last commit
  (`kept`), and that commit's record `r` names the table the change was
  computed on (`o.base`).

## What it rules out

- A change applied to a commit another process or application made after the
  write read the sink: the length would differ and the write would conflict.
- A change landing on rows another application wrote.

## What it does not cover

- The table format. That a Delta or Iceberg commit is atomic and conditional
  on the version it read is an assumption about the format.
- The data. A table is `rows plan version`, so the theorem says the change is
  applied to the right table, and the proofs about plans say the change is
  right.

## Its side conditions

Reachability only. The writers decide as `Refresh.next` does
(`python/tests/test_refresh_next.py`).

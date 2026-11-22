# `Refresh.no_corruption`

However refreshes crash, race and lose acknowledgements, a sink's table never holds a change applied to a table it was not computed from.

Lean: `Substrait.Refresh.no_corruption`, in
[`analysis/Sverify/Analysis/Refresh.lean`](../../analysis/Sverify/Analysis/Refresh.lean).
Layer: the refresh protocol of one stored node as a transition system, not a
plan: the theorem speaks of `Reachable` states. Axioms: `propext`,
`Quot.sound` ([trusted-base.md](../trusted-base.md)).

## What it says

A refresh writes a change to a sink, and a change is right only on the table
it was computed from. Processes crash with a write in flight and the write
lands late; a lost acknowledgement makes a process write again; two processes
race; another application writes the sink; a deploy changes the plan. In the
model, a change applied to any other table makes the table `corrupt`. This
theorem says no reachable state is `corrupt`, for any number of processes and
any interleaving. A refresh that is unsure replaces the table in full, and a
refresh that is sure merges the change.

## The statement, line by line

```lean
theorem Refresh.no_corruption {s : World} (h : Reachable s) : s.tbl ≠ .corrupt
```

- `s`, `h`: a state of the protocol, and the assumption that it is
  reachable (`Reachable`): the empty state, or a state a step of the protocol
  or of its environment leads to from a reachable one. The steps are a
  process starting, stopping or refreshing, preparing a write, landing it
  (with the acknowledgement lost, or failing, or finding a conflict), a
  crash, the late landing of a crashed process's write, the source changing
  (`sourceChanges`), another application writing the sink (`foreignWrite`)
  and a deploy.
- The conclusion: the sink's table `s.tbl` is not `corrupt`, the state a
  change written on the wrong table leaves.

## What it rules out

- A change applied twice or on a table another process already changed: the
  write's condition on the log it read, and the record it merges on, rule it
  out.
- A change merged onto rows another application wrote: `next` replaces
  instead (`_foreign`, #966).

## What it does not cover

- A source that is not durable. The model's source has one counter, its
  version names its contents and only grows. A source that cannot restore
  (`from_frame`), one whose versions count a process's reads, and a source
  dropped and created again with lower versions are outside the Lean model;
  the TLA+ model ([models/refresh](../../models/refresh/README.md)) checks
  the first at small scopes.
- Writers that decide otherwise. The theorem is about writers that decide as
  `Refresh.next` does; `python/tests/test_refresh_next.py` runs each of its
  cases against `Sink._commit`.
- The table format. That a Delta or Iceberg commit is atomic and conditional
  on the version it read is an assumption about the format.
- What the rows are. The data is abstract: the node's rows are a function of
  the plan and the source's version, so the theorem says a change is applied
  to the right table, and the proofs about plans say the change is right.

## Its side conditions

Reachability is the only hypothesis. That the writers decide as `Refresh.next`
and that the source is durable are the assumptions the model is built on;
`Refresh.lean`'s header lists them.

## Example

```python
import pathlib
import tempfile

import pyarrow as pa
import sverify as sv
from deltalake import DeltaTable, write_deltalake
from ibis import _
from sverify.io import DeltaSink, DeltaSource

lake = pathlib.Path(tempfile.mkdtemp())
write_deltalake(
    lake / "orders",
    pa.table({"id": [1, 2], "amount": [30, 5]}),
    configuration={"delta.enableChangeDataFeed": "true"},
)


@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1_000_000, sv.unique("id")]},
    ensures=[_.doubled >= 0],
)
def big(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


def process():
    """A new process: it builds the node from the source and the sink."""
    return DeltaSource(str(lake / "orders")).pipe(big).write(DeltaSink(str(lake / "big")))


def rows():
    return sorted(DeltaTable(lake / "big").to_pyarrow_table().to_pylist(), key=lambda r: r["id"])
```

The first process computes the table. A second process, started from the
same files, resumes from the sink's record and finds that its write is
already there:

```python
print(process().refresh().summary())
# big: computed, requires checked on data (2 proved from metadata), created v2: +1 −0
print(process().refresh().summary())
# big: resumed from ..., requires checked on data (2 proved from metadata), already committed
```

When the source changes, a new process merges the change on the record it
resumed from:

```python
write_deltalake(lake / "orders", pa.table({"id": [3], "amount": [50]}), mode="append")
print(process().refresh().summary())
# big: changes from orders v0→v1 (change feed), requires checked on 1 row(s) (2 proved from metadata), merge v3: +1 −0
print(rows())
# [{'id': 1, 'doubled': 60}, {'id': 3, 'doubled': 100}]
```

When another application has written the sink in between, the record is not
the table's newest commit, so a merge could land on rows it was not computed
from. The next process replaces the table instead:

```python
write_deltalake(lake / "big", pa.table({"id": [99], "doubled": [0]}), mode="append")
write_deltalake(lake / "orders", pa.table({"id": [4], "amount": [60]}), mode="append")
print(process().refresh().summary())
# big: computed, requires checked on data (2 proved from metadata), overwrite v5: +3 −0, the sink overwrote its table
print(rows())
# [{'id': 1, 'doubled': 60}, {'id': 3, 'doubled': 100}, {'id': 4, 'doubled': 120}]
```

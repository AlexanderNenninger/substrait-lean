# `Refresh.record_describes_table`

When the node's commit is the newest on a sink, the table is the state its record names.

Lean: `Substrait.Refresh.record_describes_table`, in
[`analysis/Sverify/Analysis/Refresh.lean`](../../analysis/Sverify/Analysis/Refresh.lean).
Layer: the refresh protocol of one stored node as a transition system, not a
plan: the theorem speaks of `Reachable` states. Axioms: `propext`,
`Quot.sound` ([trusted-base.md](../trusted-base.md)).

## What it says

Each commit a refresh writes carries a record: the plan and the source's
version the table is the state of. A reader, and the next process, trust the
record to say what the table holds. This theorem says that when the newest
commit on the sink is the node's own, which is what `kept` asks, the table is
exactly the rows the record names. If another application has written since,
the theorem says nothing, and a refresh does not trust the record
([`Refresh.no_corruption`](refresh_no_corruption.md)).

## The statement, line by line

```lean
theorem Refresh.record_describes_table {s : World} (h : Reachable s) (hk : kept s.log = true) :
    ∃ r, record s.log = some r ∧ s.tbl = r.tbl
```

- `s`, `h`: a state of the protocol, and the assumption that it is
  reachable (`Reachable`): the empty state, or a state a step of the protocol
  or of its environment leads to from a reachable one. The steps are a
  process starting, stopping or refreshing, preparing a write, landing it
  (with the acknowledgement lost, or failing, or finding a conflict), a
  crash, the late landing of a crashed process's write, the source changing
  (`sourceChanges`), another application writing the sink (`foreignWrite`)
  and a deploy.
- `hk`: the newest commit of the sink's log is the node's own (`kept`).
- The conclusion: the sink has a record `r`, the one the log reports
  (`record s.log`), and the table is the rows of that record's plan and
  version (`r.tbl`).

## What it rules out

- A record that names a state the table is not in, after the node's own last
  commit: a write that lands late, or twice, would break it, and the
  conditional commit rules them out.
- Resuming from a record that does not describe the table.

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
- A sink another application has written. Then `hk` fails, and the refresh
  replaces the table in full.

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

After a refresh, the sink's contract is the record of its last commit, and
the table is the node's rows at the source version it names:

```python
node = process()
node.refresh()
record = DeltaSink(str(lake / "big")).contract()
print(record.sources)
# {'orders': 0}
print(rows())
# [{'id': 1, 'doubled': 60}]
```

Another application then writes the sink. The node's commit is no longer
the newest, so the record no longer describes the table, and the next refresh
does not rely on it:

```python
write_deltalake(lake / "big", pa.table({"id": [99], "doubled": [0]}), mode="append")
print(len(rows()))
# 2
print(process().refresh().summary())
# big: computed, requires checked on data (2 proved from metadata), overwrite v4: +1 −0, the sink overwrote its table
print(rows())
# [{'id': 1, 'doubled': 60}]
```

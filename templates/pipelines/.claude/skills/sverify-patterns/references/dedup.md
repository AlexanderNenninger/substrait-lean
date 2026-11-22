# Deduplicate: the latest row per key

Use it when a feed repeats a key (revisions, redeliveries) and consumers want
one row per key.

## The rule

Number the rows of each key from the newest and keep the first. List every
column that decides the order, so no two rows tie.

```python
import ibis
from ibis import _

import sverify as sv

events = ibis.table({"id": "int64", "ts": "int64", "v": "int64"}, name="events")
w = ibis.window(group_by=events.id, order_by=[events.ts.desc(), events.v.desc()])
latest = events.mutate(rn=ibis.row_number().over(w)).filter(_.rn == 0).drop("rn")
```

Ibis numbers rows from 0. In SQL:

```sql
SELECT id, ts, v FROM (
  SELECT *, row_number() OVER (PARTITION BY id ORDER BY ts DESC, v DESC) AS rn FROM events
) WHERE rn = 1
```

## The contract

The output has one row per `id`. The precondition `unique(id, ts, v)` closes the
ties of the window, so the choice of row does not depend on the engine.

```python
requires = {"events": [_.ts >= 0, sv.unique("id", "ts", "v")]}
report = sv.verify(latest, requires=requires, ensures=[sv.unique("id")])
assert report.verdict == sv.Verdict.PROVED

sql = sv.sql(
    "SELECT id, ts, v FROM (SELECT *, row_number() OVER (PARTITION BY id "
    "ORDER BY ts DESC, v DESC) AS rn FROM events) WHERE rn = 1",
    events=events,
)
assert sv.verify(sql, requires=requires, ensures=[sv.unique("id")]).verdict == sv.Verdict.PROVED
```

## Refusals and suggestions

- Without `unique(id, ts, v)` the report names the key that would close the
  ties (`report.ties`) and notes that a rerun may pick another row.
- A nullable order column puts NULLs first or last depending on the engine. State
  `_.ts.notnull()` or order by a column that is never NULL.
- `ibis.row_number()` is 0-based, SQL's `row_number()` 1-based.

## As a node

```python
import pyarrow as pa
from sverify.io import StaticSource


@sv.transform(requires=requires, ensures=[sv.unique("id")])
def latest_events(events):
    w = ibis.window(group_by=events.id, order_by=[events.ts.desc(), events.v.desc()])
    return events.mutate(rn=ibis.row_number().over(w)).filter(_.rn == 0).drop("rn")


source = StaticSource(pa.table({"id": [1, 1, 2], "ts": [1, 2, 1], "v": [10, 20, 30]}), name="events")
node = latest_events(source)
node.refresh()
print(sorted(node.to_arrow().to_pylist(), key=str))  # [{'id': 1, 'ts': 2, 'v': 20}, {'id': 2, 'ts': 1, 'v': 30}]
```

Sinks and scheduled refreshes are in `sverify-pipelines`.

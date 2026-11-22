# Slowly changing dimensions over a change feed

Use it to keep the history of a row that changes: type 1 overwrites, type 2
keeps each version with its validity, type 4 keeps the current row and the
history in two tables. The history view over a change feed is tracked in #763.

## The rule

A change feed has a row per change, with the time it took effect.

- Type 1 is the latest row per key: `references/dedup.md`.
- Type 2 gives each version the next version's start as its end.
- Type 4 is type 1 for the current table and type 2 for the history table.

```python
import ibis
from ibis import _

import sverify as sv

changes = ibis.table({"key": "int64", "valid_from": "int64", "val": "string"}, name="changes")
w = ibis.window(group_by=changes.key, order_by=changes.valid_from)
history = changes.mutate(valid_to=changes.valid_from.lead().over(w))
history = history.mutate(current=history.valid_to.isnull())
```

In SQL:

```sql
SELECT *, lead(valid_from) OVER (PARTITION BY key ORDER BY valid_from) AS valid_to FROM changes
```

## The contract

A version is identified by `(key, valid_from)`, ends after it starts, and is
current exactly when it has no end.

```python
requires = {"changes": [_.key.notnull(), _.valid_from.notnull(), sv.unique("key", "valid_from")]}
ensures = [
    sv.unique("key", "valid_from"),
    _.valid_to.isnull() | (_.valid_to > _.valid_from),
    _.current.notnull(),
]
assert sv.verify(history, requires=requires, ensures=ensures).verdict == sv.Verdict.PROVED

sql = sv.sql(
    "SELECT *, lead(valid_from) OVER (PARTITION BY key ORDER BY valid_from) AS valid_to FROM changes",
    changes=changes,
)
assert sv.verify(sql, requires=requires, ensures=ensures[:2]).verdict == sv.Verdict.PROVED
```

## Refusals and suggestions

- Without `unique(key, valid_from)` two changes at one instant tie, and the
  `valid_to` of the earlier one is the engine's choice.
- That two versions of a key never overlap needs both rows of a pair, which
  the lenses do not see. Test it on the data.

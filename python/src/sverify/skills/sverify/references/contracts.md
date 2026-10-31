# Contracts in more depth

## What Lean tracks

Per output column: whether it can be NULL, integer, double and timestamp
ranges, which booleans it can be, and whether it can be a string. Filters
(`amount > 10`, `x IN (1, 2, 3)`, `x IS NOT NULL`, `x IS NULL OR x >= 0`)
refine those facts; arithmetic, `CASE`, `COALESCE`, joins and `UNION ALL`
carry them through. A non-nullable schema column is never NULL.

Join and filter conditions such as `a.ts = b.ts`, `t0 < t1`, `w1.ts = w0.ts +
60` or `value != -9999` become facts about each row, so postconditions like
`first_txn < duplicate_txn` follow. Keys survive filters, projections,
aggregates (the grouping columns are a key) and joins whose condition pins
down the other side's key.

Doubles compare as SQL engines compare them: one zero, and one NaN, equal to
itself and above every number, so `NaN > 30` is TRUE and a filter `v > 30`
keeps NaN rows. Ask for `~_.v.isnan()` if a NaN must not get through.

Not tracked: string contents, DECIMAL columns, relations beyond "column plus
constant", counts across rows.

## SQL transformations

`sv.verify` takes a SQL string with the input schemas (needs the
`datafusion` extra or Isthmus):

```python
import ibis
import sverify as sv

orders = ibis.table({"id": "int64", "amount": "int64"}, name="orders")
report = sv.verify(
    "select id, amount * 2 as doubled from orders where amount > 10",
    tables={"orders": orders},
    requires={"orders": ["amount >= 0", sv.unique("id")]},
    ensures=["doubled >= 22", sv.unique("id")],
)
assert report.proved
```

Contracts travel through a `Pipeline` only with Ibis steps; a SQL view is
maintained without guarantees.

## Composing contracts

When one contracted step feeds another, the downstream preconditions are
proved from the upstream contract instead of being checked on the data. A
broken link raises `CompositionError`:

```python
from ibis import _


@sv.transform(
    requires={"orders": [_.amount >= 0, sv.unique("id")]},
    ensures=[_.amount >= 0, _.amount.notnull(), sv.unique("id")],
)
def paid(orders):
    return orders.filter(orders.amount.notnull())


@sv.transform(requires={"t": [_.amount >= 0, _.amount.notnull()]}, ensures=[_.doubled >= 0])
def doubled(t):
    return t.select(t.id, doubled=t.amount * 2)


expr = doubled(paid(orders))
print(doubled.last_report)  # requires paid: ... (what `paid` guarantees)
```

`sv.contracts.provenance(expr)` shows what a contracted result assumed and
guarantees.

ASOF joins (`sv.asof_join`) are in the `sverify-engines` skill.

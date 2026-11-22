# Running balance and FIFO matching

Use it for an account's balance after each entry, or to match sales to buys in
the order the lots arrived.

## The rule

A running sum over the account's entries in order gives the balance.

```python
import ibis
from ibis import _

import sverify as sv

tx = ibis.table({"acct": "string", "seq": "int64", "amt": "int64"}, name="tx")
w = ibis.window(group_by=tx.acct, order_by=tx.seq, rows=(None, 0))
balance = tx.mutate(balance=tx.amt.sum().over(w))
```

In SQL:

```sql
SELECT *, sum(amt) OVER (PARTITION BY acct ORDER BY seq
  ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW) AS balance FROM tx
```

## The contract

`(acct, seq)` is a key and, for deposits, the balance is never negative. A
range of the amounts and a row cap rule out an overflow.

```python
requires = {
    "tx": [
        _.acct.notnull(),
        _.seq.notnull(),
        _.amt.notnull(),
        _.amt >= 0,
        _.amt <= 10**9,
        sv.unique("acct", "seq"),
        sv.max_rows(10**6),
    ]
}
ensures = [sv.unique("acct", "seq"), _.balance.isnull() | (_.balance >= 0)]
assert sv.verify(balance, requires=requires, ensures=ensures).verdict == sv.Verdict.PROVED

sql = sv.sql(
    "SELECT *, sum(amt) OVER (PARTITION BY acct ORDER BY seq "
    "ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW) AS balance FROM tx",
    tx=tx,
)
assert sv.verify(sql, requires=requires, ensures=ensures).verdict == sv.Verdict.PROVED
```

With signed amounts the balance has no sign to prove. Bound the amounts and
the row count, and the contract proves the key and the absence of an overflow.

## FIFO matching

Give each lot the interval `[cum - qty, cum)` of the cumulative quantity. A buy
and a sale match on the overlap of their intervals. The cumulative total is
a window value, which the proof does not bound, so the lots come with their
cumulative quantity as a column, bounded in `requires`, and checked on the data
when the node refreshes.

```python
buys = ibis.table({"id": "int64", "qty": "int64", "px": "int64", "cum": "int64"}, name="buys")
sells = ibis.table({"id": "int64", "qty": "int64", "px": "int64", "cum": "int64"}, name="sells")
b = buys.mutate(lo=buys.cum - buys.qty)
s = sells.mutate(lo=sells.cum - sells.qty)
j = b.join(s, how="cross", rname="{name}_sell")
overlap = ibis.greatest(ibis.least(j.cum, j.cum_sell) - ibis.greatest(j.lo, j.lo_sell), 0)
matches = j.select(buy=j.id, sell=j.id_sell, matched=overlap, pnl=overlap * (j.px_sell - j.px))

side = [
    _.id.notnull(),
    _.qty.notnull(),
    _.px.notnull(),
    _.cum.notnull(),
    _.qty.between(0, 10**6),
    _.px.between(0, 10**6),
    _.cum.between(0, 10**10),
    sv.unique("id"),
    sv.max_rows(10**4),
]
report = sv.verify(
    matches,
    requires={"buys": side, "sells": side},
    ensures=[_.matched >= 0, _.pnl.isnull() | _.pnl.between(-2 * 10**16, 2 * 10**16)],
)
assert report.verdict == sv.Verdict.PROVED
```

## Refusals and suggestions

- Computing `cum` inside the same expression (`qty.sum().over(...)`, then
  `cum - qty`) lists an overflow: the proof finds no bound on a window value.
  Compute it in an upstream node and state its range in `requires` here.
- The cross join is quadratic. Cap both sides with `max_rows`.

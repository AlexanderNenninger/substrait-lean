# Reconcile two systems, and double entries

Use it to compare a ledger with a bank statement, or to check that two
copies of a table agree. A full outer join keeps the rows only one side has.

## The rule

Join on the key, label each row, and keep the exceptions.

```python
import ibis
from ibis import _

import sverify as sv

ledger = ibis.table({"id": "int64", "amt": "int64"}, name="ledger")
bank = ibis.table({"id": "int64", "amt": "int64"}, name="bank")
joined = ledger.join(bank, ledger.id == bank.id, how="outer", rname="{name}_bank")
rows = joined.select(
    id=ibis.coalesce(joined.id, joined.id_bank), ledger=joined.amt, bank=joined.amt_bank
)
labelled = rows.mutate(
    status=ibis.cases(
        (rows.ledger.isnull(), "missing_in_ledger"),
        (rows.bank.isnull(), "missing_in_bank"),
        (rows.ledger == rows.bank, "matched"),
        else_="amount_differs",
    )
)
exceptions = labelled.filter(_.status != "matched")
```

In SQL:

```sql
SELECT coalesce(l.id, b.id) AS id, l.amt AS ledger, b.amt AS bank,
  CASE WHEN l.amt IS NULL THEN 'missing_in_ledger' WHEN b.amt IS NULL THEN 'missing_in_bank'
       WHEN l.amt = b.amt THEN 'matched' ELSE 'amount_differs' END AS status
FROM ledger l FULL OUTER JOIN bank b ON l.id = b.id
```

## The contract

Every row has a status from the four values, and the exceptions never hold a
matched row. A key per side keeps the join from multiplying rows.

```python
requires = {
    "ledger": [_.id.notnull(), _.amt.notnull(), sv.unique("id")],
    "bank": [_.id.notnull(), _.amt.notnull(), sv.unique("id")],
}
statuses = ["matched", "amount_differs", "missing_in_bank", "missing_in_ledger"]
report = sv.verify(
    labelled, requires=requires, ensures=[_.status.notnull(), _.status.isin(statuses)]
)
assert report.verdict == sv.Verdict.PROVED
only = sv.verify(exceptions, requires=requires, ensures=[_.status != "matched"])
assert only.verdict == sv.Verdict.PROVED

sql = sv.sql(
    "SELECT coalesce(l.id, b.id) AS id, l.amt AS ledger, b.amt AS bank, "
    "CASE WHEN l.amt IS NULL THEN 'missing_in_ledger' WHEN b.amt IS NULL THEN 'missing_in_bank' "
    "WHEN l.amt = b.amt THEN 'matched' ELSE 'amount_differs' END AS status "
    "FROM ledger l FULL OUTER JOIN bank b ON l.id = b.id",
    ledger=ledger,
    bank=bank,
)
assert (
    sv.verify(sql, requires=requires, ensures=[_.status.isin(statuses)]).verdict
    == sv.Verdict.PROVED
)
```

## Double entries

A transfer posts a debit and a credit of the same amount: two rows of a signed
`amount`, one per side.

```python
transfers = ibis.table(
    {"id": "int64", "src": "string", "dst": "string", "amount": "int64"}, name="transfers"
)
debit = transfers.select("id", acct=transfers.src, amount=-transfers.amount)
credit = transfers.select("id", acct=transfers.dst, amount=transfers.amount)
entries = debit.union(credit, distinct=False)
posted = {
    "transfers": [
        _.id.notnull(),
        _.src.notnull(),
        _.dst.notnull(),
        _.amount > 0,
        _.amount <= 10**9,
    ]
}
report = sv.verify(
    entries, requires=posted, ensures=[_.acct.notnull(), _.amount.between(-(10**9), 10**9)]
)
assert report.verdict == sv.Verdict.PROVED
```

That the entries of a transfer sum to zero relates two rows, which the proof does
not see. Check it on the data, or reconcile the totals per account with the rule above.

## Refusals and suggestions

- `ledger.notnull() | bank.notnull()` is unproved: the proof does not know an
  outer join row has one side. Put the claim in `status`.
- The joined key is `coalesce(...)`: no key is proved on the output, and the
  report says no key on an input makes it one.

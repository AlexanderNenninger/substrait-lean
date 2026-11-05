"""Duplicate card payments (tour notebook 1).

The same card paying the same amount at the same merchant twice within five
minutes. Every postcondition is proved: hover the transform for the report
and the route on each engine.
"""

import datetime as dt

import ibis
import sverify as sv
from ibis import _

transactions = ibis.table(
    {
        "txn_id": "!int64",
        "card_id": "!int64",
        "merchant": "string",
        "amount_cents": "!int64",
        "ts": "!timestamp",
    },
    name="transactions",
)


def find_duplicates(transactions):
    a, b = transactions, transactions.view()
    return a.join(
        b,
        (a.card_id == b.card_id)
        & (a.merchant == b.merchant)
        & (a.amount_cents == b.amount_cents)
        & (a.txn_id < b.txn_id)
        & (b.ts >= a.ts)
        & (b.ts <= a.ts + ibis.interval(minutes=5)),
    ).select(
        first_txn=a.txn_id,
        duplicate_txn=b.txn_id,
        card_id=a.card_id,
        merchant=a.merchant,
        amount_cents=a.amount_cents,
        first_ts=a.ts,
        duplicate_ts=b.ts,
    )


REQUIRES = {
    "transactions": [
        sv.unique("txn_id"),
        _.amount_cents >= 0,
        _.ts < dt.datetime(2100, 1, 1),
    ]
}
ENSURES = [
    sv.unique("first_txn", "duplicate_txn"),
    _.first_txn < _.duplicate_txn,
    _.merchant.notnull(),
    _.amount_cents >= 0,
    _.first_ts <= _.duplicate_ts,
]


@sv.transform(requires=REQUIRES, ensures=ENSURES)
def duplicate_payments(transactions):
    return find_duplicates(transactions)

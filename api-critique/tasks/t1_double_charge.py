"""Task 1: flag double charges (same card, merchant and amount within five minutes).

What a payments engineer would write first, from the README and examples.md.
"""

import datetime as dt

import pyarrow as pa
from ibis import _

import sverify as sv
from sverify.errors import VerificationError
from sverify.io import StaticSource

t0 = dt.datetime(2026, 11, 5, 9, 0)
payments = StaticSource(
    pa.table(
        {
            "txn_id": [1, 2, 3, 4],
            "card": ["c1", "c1", "c2", "c1"],
            "merchant": ["cafe", "cafe", "cafe", "cafe"],
            "amount_cents": [350, 350, 350, 350],
            "ts": [t0, t0 + dt.timedelta(minutes=2), t0, t0 + dt.timedelta(minutes=30)],
        }
    ),
    name="payments",
)


# Attempt 1: the obvious self-join, with the contract I care about.
@sv.transform(
    requires={"payments": [sv.unique("txn_id"), _.amount_cents >= 0]},
    ensures=[_.first_txn < _.dup_txn, sv.unique("dup_txn")],
)
def double_charges(payments):
    a = payments
    b = payments.view()
    j = a.join(
        b,
        (a.card == b.card)
        & (a.merchant == b.merchant)
        & (a.amount_cents == b.amount_cents)
        & (a.ts < b.ts)
        & (b.ts <= a.ts + sv_interval),
    )
    return j.select(first_txn=a.txn_id, dup_txn=b.txn_id, card=a.card)


import ibis  # noqa: E402

sv_interval = ibis.interval(minutes=5)

try:
    node = payments.pipe(double_charges)
    print("attempt 1 proved")
    print(double_charges.last_report)
except VerificationError as e:
    print("attempt 1 refused:\n", e)


# Attempt 2: relax the key claim; a duplicate can follow two earlier charges.
@sv.transform(
    requires={"payments": [sv.unique("txn_id"), _.amount_cents >= 0]},
    ensures=[_.first_txn < _.dup_txn],
)
def double_charges2(payments):
    a = payments
    b = payments.view()
    j = a.join(
        b,
        (a.card == b.card)
        & (a.merchant == b.merchant)
        & (a.amount_cents == b.amount_cents)
        & (a.ts < b.ts)
        & (b.ts <= a.ts + ibis.interval(minutes=5)),
    )
    return j.select(first_txn=a.txn_id, dup_txn=b.txn_id, card=a.card)


try:
    node = payments.pipe(double_charges2)
    print("attempt 2 proved")
    print(double_charges2.last_report)
    print(node.refresh())
    print(node.to_arrow().to_pylist())
except VerificationError as e:
    print("attempt 2 refused:\n", e)


# Attempt 3: state the ordering via the timestamps, which is what the join guarantees.
@sv.transform(
    requires={"payments": [sv.unique("txn_id"), _.amount_cents >= 0, _.ts.notnull()]},
    ensures=[_.first_ts < _.dup_ts, _.first_txn.notnull()],
)
def double_charges3(payments):
    a = payments
    b = payments.view()
    j = a.join(
        b,
        (a.card == b.card)
        & (a.merchant == b.merchant)
        & (a.amount_cents == b.amount_cents)
        & (a.ts < b.ts)
        & (b.ts <= a.ts + ibis.interval(minutes=5)),
    )
    return j.select(first_txn=a.txn_id, dup_txn=b.txn_id, first_ts=a.ts, dup_ts=b.ts)


try:
    node3 = payments.pipe(double_charges3)
    print("attempt 3 proved")
    print(double_charges3.last_report)
    node3.refresh()
    print(node3.to_arrow().to_pylist())
    payments.apply(
        sv.Changes(inserts=[(5, "c2", "cafe", 350, t0 + dt.timedelta(minutes=1))])
    )
    print(node3.refresh().summary())
    print(node3.to_arrow().to_pylist())
except VerificationError as e:
    print("attempt 3 refused:\n", e)


# Attempt 4: follow the messages: declare the inferred bound and NOT NULL ids.
@sv.transform(
    requires={
        "payments": [
            sv.unique("txn_id"),
            _.txn_id.notnull(),
            _.amount_cents >= 0,
            _.ts.notnull(),
            _.ts < dt.datetime(9999, 1, 1),
        ]
    },
    ensures=[_.first_ts < _.dup_ts, _.first_txn.notnull(), _.dup_ts - _.first_ts <= ibis.interval(seconds=300)],
)
def double_charges4(payments):
    a = payments
    b = payments.view()
    j = a.join(
        b,
        (a.card == b.card)
        & (a.merchant == b.merchant)
        & (a.amount_cents == b.amount_cents)
        & (a.ts < b.ts)
        & (b.ts <= a.ts + ibis.interval(minutes=5)),
    )
    return j.select(first_txn=a.txn_id, dup_txn=b.txn_id, first_ts=a.ts, dup_ts=b.ts)


try:
    node4 = payments.pipe(double_charges4)
    print("attempt 4 proved")
    print(double_charges4.last_report)
    print(node4.refresh())
    print(node4.to_arrow().to_pylist())
    payments.apply(sv.Changes(inserts=[(5, "c2", "cafe", 350, t0 + dt.timedelta(minutes=1))]))
    print(node4.refresh().summary())
    print(node4.to_arrow().to_pylist())
    print(node4.refresh(engine="polars"))
except VerificationError as e:
    print("attempt 4 refused:\n", e)

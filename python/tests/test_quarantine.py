"""`on_violation`: rows that break a source's preconditions set aside, or the
batch held (#184).

The rule (`sverify._quarantine`): a row is kept when every row condition is
TRUE on it and, among those rows, its key occurs once. The tests compare
each refresh with that rule computed here in plain Python from the source
table alone, so a batch-by-batch refresh must agree with it.
"""

from __future__ import annotations

import json
import math
from collections import Counter
from datetime import date
from decimal import Decimal

import pyarrow as pa
import pytest
from deltalake import DeltaTable, write_deltalake
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify import _quarantine
from sverify.errors import PreconditionError
from sverify.incremental import Changes
from sverify.io import DeltaSink, DeltaSource, StaticSource

SCHEMA = pa.schema([("id", pa.int64()), ("amount", pa.int64())])


def table(rows) -> pa.Table:
    return pa.Table.from_pylist([dict(zip(SCHEMA.names, r, strict=True)) for r in rows], SCHEMA)


def make(policy="quarantine", keys=True):
    requires = [_.amount >= 0] + ([sv.unique("id")] if keys else [])

    @sv.transform(
        requires={"orders": requires},
        ensures=[_.amount >= 0, _.amount.notnull()] + ([sv.unique("id")] if keys else []),
        on_violation=policy,
    )
    def paid(orders):
        return orders.filter(orders.amount.notnull()).select("id", "amount")

    return paid


def kept(rows, keys=True) -> list[tuple]:
    """The rule, in plain Python."""
    ok = [r for r in rows if r[1] is not None and r[1] >= 0]
    if not keys:
        return ok
    ids = Counter(r[0] for r in ok)
    return [r for r in ok if ids[r[0]] == 1]


def bag(t: pa.Table, cols=("id", "amount")) -> Counter:
    return Counter(tuple(r[c] for c in cols) for r in t.to_pylist())


# -- the rule, batch by batch ---------------------------------------------------

row = st.tuples(st.integers(0, 4), st.one_of(st.none(), st.integers(-2, 3)))


@st.composite
def histories(draw):
    first = draw(st.lists(row, max_size=8))
    current = list(first)
    batches = []
    for _i in range(draw(st.integers(1, 4))):
        dels = draw(st.lists(st.sampled_from(current), max_size=3, unique=True)) if current else []
        ins = draw(st.lists(row, max_size=4))
        for d in dels:
            current.remove(d)
        current += ins
        batches.append((ins, dels))
    return first, batches


@pytest.mark.parametrize("keys", [True, False])
@given(history=histories())
@settings(
    max_examples=60, deadline=None, suppress_health_check=[HealthCheck.too_slow]
)
def test_refresh_keeps_the_rows_the_rule_keeps(keys, history):
    first, batches = history
    orders = StaticSource(table(first), name="orders")
    node = orders.pipe(make(keys=keys))
    node.refresh()
    rows = list(first)
    for ins, dels in [([], []), *batches]:
        if ins or dels:
            orders.apply(Changes(inserts=table(ins), deletes=table(dels)))
            for d in dels:
                rows.remove(d)
            rows += ins
            node.refresh()
        want = Counter(kept(rows, keys))
        got = bag(node.to_arrow())
        assert got == want
        # The contract holds on what the node read.
        assert all(a is not None and a >= 0 for _i, a in got)
        if keys:
            assert all(n == 1 for n in Counter(i for i, _a in got.elements()).values())
        # The rows set aside are the others.
        held = node.quarantined()
        held_bag = bag(held) if held.num_columns else Counter()
        assert held_bag == Counter(rows) - Counter(kept(rows, keys))


def test_split_batch_matches_split_snapshot():
    con = sv.connect()
    conds, keys = [_.amount >= 0], [sv.unique("id")]
    before = table([(1, 5), (2, -1), (3, 1), (3, 2), (4, None)])
    k, q = _quarantine.split_snapshot(con, before, conds, keys, 0)
    assert bag(k) == Counter({(1, 5): 1})
    change = pa.concat_tables(
        [
            _quarantine.weighted(table([(5, 1), (1, 2)]), 1),
            _quarantine.weighted(table([(3, 2), (2, -1)]), -1),
        ]
    )
    moves = _quarantine.split_batch(con, k, q, change, conds, keys, 1)
    after = table([(1, 5), (3, 1), (4, None), (5, 1), (1, 2)])
    k2, q2 = _quarantine.split_snapshot(con, after, conds, keys, 1)
    new_kept = Counter(bag(k)) + Counter(
        {(r["id"], r["amount"]): r["__weight"] for r in moves.kept.to_pylist()}
    )
    assert +new_kept == bag(k2) == Counter({(3, 1): 1, (5, 1): 1})
    assert moves.quarantined.entries.keys() == q2.entries.keys()
    assert moves.released == 1  # (3, 1): its id is on one row again
    assert moves.deleted == 2  # (2, -1) and (3, 2) were set aside, and are deleted upstream
    # (1, 5) went from kept to set aside, with the new (1, 2).
    assert sum(e.copies for e in moves.set_aside) == 2


# -- what a refresh reports -------------------------------------------------------


def test_reports_say_what_was_set_aside():
    orders = StaticSource(table([(1, 30), (2, -5), (3, 7), (3, 8)]), name="orders")
    node = orders.pipe(make())
    r = node.refresh()
    entry = r[node.name]
    assert entry.set_aside == 3
    (q,) = entry.quarantine
    assert q.by_condition == {"(_.amount >= 0)": 1, "unique(id)": 2}
    assert q.examples is not None and q.examples.num_rows == 3
    assert r.outcome == "quarantined"
    assert "3 row(s) of orders set aside" in str(r)
    alert = r.alert()
    assert alert is not None and "(_.amount >= 0)" in alert and "| id | amount |" in alert
    doc = json.loads(r.to_json())
    assert doc["format"] == 1 and doc["outcome"] == "quarantined"
    assert doc["nodes"][0]["quarantine"]["set_aside"] == 3
    # An upstream fix: the negative row deleted, one of the repeated ids too.
    orders.apply(Changes(inserts=table([(2, 5)]), deletes=table([(2, -5), (3, 8)])))
    r = node.refresh()
    (q,) = r[node.name].quarantine
    assert (q.set_aside, q.released, q.deleted, q.held) == (0, 1, 2, 0)
    assert r.outcome == "ok" and r.alert() is None
    assert bag(node.to_arrow()) == Counter({(1, 30): 1, (2, 5): 1, (3, 7): 1})


def test_a_new_duplicate_retracts_the_kept_row():
    orders = StaticSource(table([(1, 30)]), name="orders")
    node = orders.pipe(make())
    node.refresh()
    orders.apply(Changes(inserts=table([(1, 31)])))
    node.refresh()
    assert node.to_arrow().num_rows == 0
    assert bag(node.quarantined()) == Counter({(1, 30): 1, (1, 31): 1})
    orders.apply(Changes(deletes=table([(1, 31)])))
    node.refresh()
    assert bag(node.to_arrow()) == Counter({(1, 30): 1})


# -- the default, and which policy holds ------------------------------------------


def test_the_default_still_raises():
    orders = StaticSource(table([(1, 30), (2, -5)]), name="orders")
    with pytest.raises(PreconditionError, match=r"violate \(_.amount >= 0\)"):
        orders.pipe(make(policy=None)).refresh()
    orders = StaticSource(table([(1, 30)]), name="orders")
    node = orders.pipe(make(policy=None))
    node.refresh()
    orders.apply(Changes(inserts=table([(2, -5)])))
    with pytest.raises(PreconditionError, match=r"violate \(_.amount >= 0\)"):
        node.refresh()
    assert bag(node.to_arrow()) == Counter({(1, 30): 1})


def test_the_source_sets_the_policy_unless_the_transform_does():
    orders = StaticSource(table([(1, 30), (2, -5)]), name="orders", on_violation="quarantine")
    node = orders.pipe(make(policy=None))
    assert node.refresh().outcome == "quarantined"
    orders = StaticSource(table([(1, 30), (2, -5)]), name="orders", on_violation="quarantine")
    with pytest.raises(PreconditionError):
        orders.pipe(make(policy="raise")).refresh()


def test_the_strictest_policy_wins():
    assert _quarantine.strictest(["quarantine", "skip_batch"]) == "skip_batch"
    assert _quarantine.resolve([None, "quarantine"], None) == "raise"
    assert _quarantine.resolve([None, "quarantine"], "quarantine") == "quarantine"
    assert _quarantine.resolve(["skip_batch"], "quarantine") == "skip_batch"
    with pytest.raises(ValueError, match="on_violation must be one of"):
        sv.transform(on_violation="ignore")  # type: ignore[arg-type]


# -- skip_batch and holds -----------------------------------------------------------


def test_skip_batch_holds_the_node_until_the_source_is_fixed():
    orders = StaticSource(table([(1, 30)]), name="orders")
    node = orders.pipe(make(policy="skip_batch"))
    node.refresh()
    orders.apply(Changes(inserts=table([(2, -5), (3, 1)])))
    r = node.refresh()
    entry = r[node.name]
    assert r.outcome == "held" and entry.held is not None
    assert "violate (_.amount >= 0)" in entry.held and "orders@v0" in entry.held
    assert entry.held_error.rows.num_rows == 1
    assert bag(node.to_arrow()) == Counter({(1, 30): 1})
    assert node.versions == {"orders": 0}
    # The next refresh reads the batch again; fixed, it goes through.
    orders.apply(Changes(deletes=table([(2, -5)])))
    r = node.refresh()
    assert r.outcome == "ok"
    assert bag(node.to_arrow()) == Counter({(1, 30): 1, (3, 1): 1})


def test_skip_batch_on_the_first_load_leaves_downstream_waiting(tmp_path):
    orders = StaticSource(table([(1, 30), (2, -5)]), name="orders")
    p = orders.pipe(make(policy="skip_batch")).write(DeltaSink(str(tmp_path / "paid")))

    @sv.transform()
    def total(t):
        return t.aggregate(total=t.amount.sum())

    top = p.pipe(total)
    r = top.refresh()
    assert [s.held is not None for s in r.nodes] == [True, True]
    assert r.nodes[1].held == "waiting for paid"
    assert r.outcome == "held"


def test_a_condition_without_a_row_rule_holds_under_quarantine():
    @sv.transform(requires={"orders": [sv.max_rows(2)]}, on_violation="quarantine")
    def capped(orders):
        return orders

    orders = StaticSource(table([(1, 30)]), name="orders")
    node = orders.pipe(capped)
    node.refresh()
    orders.apply(Changes(inserts=table([(2, 1), (3, 1)])))
    r = node.refresh()
    assert r.outcome == "held" and "max_rows(2)" in r[node.name].held


# -- the quarantine table ------------------------------------------------------------


def test_the_quarantine_table_next_to_the_sink(tmp_path):
    src = tmp_path / "orders"
    write_deltalake(
        src,
        table([(1, 30), (2, -5), (3, 7)]),
        configuration={"delta.enableChangeDataFeed": "true"},
    )

    def job():
        source = DeltaSource(str(src), on_violation="quarantine")
        return source.pipe(make(policy=None)).write(DeltaSink(str(tmp_path / "paid")))

    r = job().refresh()
    assert r[r.nodes[0].node].quarantine_table == str(tmp_path / "paid_quarantine")
    q = DeltaTable(tmp_path / "paid_quarantine")
    rows = q.to_pyarrow_table().to_pylist()
    assert [_quarantine.decode_row(x["row"]) for x in rows] == [{"id": 2, "amount": -5}]
    assert rows[0]["conditions"] == ["(_.amount >= 0)"] and rows[0]["source_version"] == 0
    assert q.to_pyarrow_table().schema.equals(_quarantine.TABLE_SCHEMA, check_metadata=False)
    record = next(
        json.loads(c[_quarantine.RECORD_KEY]) for c in q.history() if _quarantine.RECORD_KEY in c
    )
    assert record == {"format": 1, "node": "paid", "epoch": 0, "sources": {"orders": 0}}
    first_at = rows[0]["set_aside_at"]
    # A restarted job resumes; the rows set aside keep when they were.
    write_deltalake(src, table([(4, 1), (5, -1)]), mode="append")
    r = job().refresh()
    (entry,) = r.nodes
    assert sum(q.set_aside for q in entry.quarantine) == 1
    rows = DeltaTable(tmp_path / "paid_quarantine").to_pyarrow_table().to_pylist()
    by_row = {x["row"]: x for x in rows}
    assert by_row[_quarantine.encode_row({"id": 2, "amount": -5})]["set_aside_at"] == first_at
    assert len(rows) == 2
    # A quiet refresh writes neither table.
    version = DeltaTable(tmp_path / "paid_quarantine").version()
    job_ = job()
    job_.refresh()
    job_.refresh()
    assert DeltaTable(tmp_path / "paid_quarantine").version() == version


def test_quarantine_false_keeps_the_rows_in_memory(tmp_path):
    orders = StaticSource(table([(1, 30), (2, -5)]), name="orders")
    node = orders.pipe(make()).write(DeltaSink(str(tmp_path / "paid")), quarantine=False)
    r = node.refresh()
    assert r.nodes[0].quarantine_table is None
    assert not (tmp_path / "paid_quarantine").exists()
    assert bag(node.quarantined()) == Counter({(2, -5): 1})


@pytest.mark.parametrize(
    "value",
    [
        {"d": date(2026, 11, 5), "x": Decimal("1.50"), "f": math.inf, "b": b"\x00"},
        {"l": [1, None], "s": {"a": "x"}},
    ],
)
def test_rows_round_trip_through_json(value):
    assert _quarantine.decode_row(_quarantine.encode_row(value)) == value
    nan = _quarantine.decode_row(_quarantine.encode_row({"n": math.nan}))
    assert math.isnan(nan["n"])

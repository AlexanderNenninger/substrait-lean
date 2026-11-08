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
from typing import Any

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


def make(policy: Any = "quarantine", keys: bool = True) -> Any:
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
@settings(max_examples=60, deadline=None, suppress_health_check=[HealthCheck.too_slow])
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
    assert entry.quarantined == 3
    (q,) = entry.quarantine
    assert q.by_condition == {"(_.amount >= 0)": 1, "unique(id)": 2}
    assert q.examples is not None and q.examples.num_rows == 3
    assert r.outcome == "quarantined"
    assert "orders: 3 row(s) quarantined" in str(r)
    alert = r.alert()
    assert alert is not None and "(_.amount >= 0)" in alert and "| id |" not in alert
    assert "| id | amount |" in (r.alert(rows=True) or "")
    doc = json.loads(r.to_json())
    assert doc["format"] == 1 and doc["outcome"] == "quarantined"
    assert doc["nodes"][0]["quarantined"] == 3
    # Rows of the data leave the process only when asked (#887).
    assert doc["nodes"][0]["quarantine"][0]["examples"] == []
    (shown,) = json.loads(r.to_json(examples=True))["nodes"][0]["quarantine"]
    assert {e["id"] for e in shown["examples"]} == {2, 3}
    # An upstream fix: the negative row deleted, one of the repeated ids too.
    orders.apply(Changes(inserts=table([(2, 5)]), deletes=table([(2, -5), (3, 8)])))
    r = node.refresh()
    (q,) = r[node.name].quarantine
    assert (q.quarantined, q.released, q.deleted, q.total) == (0, 1, 2, 0)
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
        orders.pipe(make(policy="error")).refresh()


def test_the_strictest_policy_wins():
    assert _quarantine.strictest(["quarantine", "hold"]) == "hold"
    assert _quarantine.resolve([None, "quarantine"], None) == "error"
    assert _quarantine.resolve([None, "quarantine"], "quarantine") == "quarantine"
    assert _quarantine.resolve(["hold"], "quarantine") == "hold"
    with pytest.raises(ValueError, match="on_violation must be one of"):
        sv.transform(on_violation="ignore")  # type: ignore[arg-type]


# -- hold and holds -----------------------------------------------------------


def test_hold_holds_the_node_until_the_source_is_fixed():
    orders = StaticSource(table([(1, 30)]), name="orders")
    node = orders.pipe(make(policy="hold"))
    node.refresh()
    orders.apply(Changes(inserts=table([(2, -5), (3, 1)])))
    r = node.refresh()
    entry = r[node.name]
    assert r.outcome == "held" and entry.held is not None
    assert "violate (_.amount >= 0)" in entry.held and "orders@v0" in entry.held
    assert isinstance(entry.held_error, PreconditionError)
    assert entry.held_error.rows is not None and entry.held_error.rows.num_rows == 1
    assert bag(node.to_arrow()) == Counter({(1, 30): 1})
    assert node.versions == {"orders": 0}
    # The next refresh reads the batch again; fixed, it goes through.
    orders.apply(Changes(deletes=table([(2, -5)])))
    r = node.refresh()
    assert r.outcome == "ok"
    assert bag(node.to_arrow()) == Counter({(1, 30): 1, (3, 1): 1})


def test_hold_on_the_first_load_leaves_downstream_waiting(tmp_path):
    orders = StaticSource(table([(1, 30), (2, -5)]), name="orders")
    p = orders.pipe(make(policy="hold")).write(DeltaSink(str(tmp_path / "paid")))

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
    held = r[node.name].held
    assert r.outcome == "held" and held is not None and "max_rows(2)" in held


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
    assert record == {
        "$schema": _quarantine.SCHEMA,
        "format": 1,
        "node": "paid",
        "epoch": 0,
        "sources": {"orders": 0},
    }
    first_at = rows[0]["quarantined_at"]
    # A restarted job resumes; the rows set aside keep when they were.
    write_deltalake(src, table([(4, 1), (5, -1)]), mode="append")
    r = job().refresh()
    (entry,) = r.nodes
    assert sum(q.quarantined for q in entry.quarantine) == 1
    rows = DeltaTable(tmp_path / "paid_quarantine").to_pyarrow_table().to_pylist()
    by_row = {x["row"]: x for x in rows}
    assert by_row[_quarantine.encode_row({"id": 2, "amount": -5})]["quarantined_at"] == first_at
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


# -- a breaking upstream change -------------------------------------------------------


def test_a_breaking_schema_change_names_the_column_version_and_contract(tmp_path):
    from _pipelines import make_orders, paid
    from sverify.errors import SchemaError

    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    node = paid(src)
    node.refresh()
    nullable = pa.schema([("id", pa.int64()), ("customer", pa.string()), ("amount", pa.int64())])
    rows = pa.Table.from_pylist(
        [
            {"id": 1, "customer": "ada", "amount": 5},
            {"id": None, "customer": "cy", "amount": 3},
        ],
        nullable,
    )
    write_deltalake(src.uri, rows, mode="overwrite", schema_mode="overwrite")
    with pytest.raises(SchemaError) as e:
        node.refresh()
    first = str(e.value).splitlines()[0]
    assert first.startswith("`orders.id` became nullable at v2, and the new rows have NULLs")
    assert "`paid` requires _.id.notnull(), unique(id)" in first
    assert "handle NULLs in `paid`" in first


def test_the_quarantine_table_next_to_an_iceberg_sink(tmp_path):
    pytest.importorskip("pyiceberg")
    from pyiceberg.catalog.sql import SqlCatalog

    from sverify.io import IcebergSink

    cat = SqlCatalog("q", uri=f"sqlite:///{tmp_path}/catalog.db", warehouse=f"file://{tmp_path}")
    cat.create_namespace("db")
    orders = StaticSource(table([(1, 30), (2, -5)]), name="orders")
    node = orders.pipe(make()).write(IcebergSink(cat, "db.paid"))
    node.refresh()
    q = cat.load_table("db.paid_quarantine")
    rows = q.scan().to_arrow().to_pylist()
    assert [_quarantine.decode_row(r["row"]) for r in rows] == [{"id": 2, "amount": -5}]
    snap = q.current_snapshot()
    assert snap is not None and snap.summary is not None
    record = json.loads(str(snap.summary[_quarantine.RECORD_KEY]))
    assert record["node"] == "paid" and record["format"] == 1
    # Fixed upstream: the table empties.
    orders.apply(Changes(deletes=table([(2, -5)])))
    node.refresh()
    assert cat.load_table("db.paid_quarantine").scan().to_arrow().num_rows == 0


def test_a_node_without_quarantine_writes_no_quarantine_table(tmp_path):
    orders = StaticSource(table([(1, 30)]), name="orders")
    orders.pipe(make(policy=None)).write(DeltaSink(str(tmp_path / "paid"))).refresh()
    assert not (tmp_path / "paid_quarantine").exists()


# -- one vocabulary for the on_* parameters (API review C1, C2) ---------------------


def test_old_spellings_of_on_unproved_and_on_inferred_warn():
    with pytest.warns(DeprecationWarning, match='on_unproved="check"'):
        t = sv.transform(on_unproved="runtime")(lambda orders: orders)  # type: ignore[arg-type]
    assert t.on_unproved == "check"
    import ibis

    orders = ibis.table({"a": "int64", "b": "int64"}, name="orders")
    with pytest.warns(DeprecationWarning, match='on_inferred="ignore"'):
        report = sv.verify(orders.select(r=orders.a // orders.b), on_inferred="silent")  # type: ignore[arg-type]
    assert report.proved


def test_check_requires_false_refuses_an_on_violation():
    with pytest.raises(ValueError, match="check_requires=False"):
        sv.transform(check_requires=False, on_violation="quarantine")
    sv.transform(check_requires=False, on_violation="error")


def test_quarantine_true_is_refused(tmp_path):
    orders = StaticSource(table([(1, 30)]), name="orders")
    with pytest.raises(TypeError, match="quarantine="):
        orders.pipe(make()).write(DeltaSink(str(tmp_path / "paid")), quarantine=True)  # type: ignore[arg-type]

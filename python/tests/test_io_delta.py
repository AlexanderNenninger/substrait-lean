"""Delta Lake tables as change sources (CDF), sources of preconditions and
sinks, on local tables in temporary directories."""

from datetime import datetime

import ibis
import pyarrow as pa
import pytest
from deltalake import DeltaTable, write_deltalake
from ibis import _

import sverify as sv
from sverify.contracts import ON_DATA, SCHEMA
from sverify.engine import Engine
from sverify.incremental import AuditError
from sverify.io import DeltaSink, DeltaSource

SCHEMA_ORDERS = pa.schema(
    [
        pa.field("id", pa.int64(), nullable=False),
        pa.field("customer", pa.string()),
        pa.field("amount", pa.int64()),
    ]
)


def orders_table(rows):
    return pa.Table.from_pylist(
        [dict(zip(SCHEMA_ORDERS.names, r, strict=True)) for r in rows], schema=SCHEMA_ORDERS
    )


def make_orders(path, rows, *, cdf=True, constraints=None):
    DeltaTable.create(
        path,
        SCHEMA_ORDERS,
        configuration={"delta.enableChangeDataFeed": "true"} if cdf else None,
    )
    dt = DeltaTable(path)
    if constraints:
        dt.alter.add_constraint(constraints)
    write_deltalake(path, orders_table(rows), mode="append")
    return DeltaSource(path)


@sv.transform(
    requires={"orders": [_.amount >= 0, _.id.notnull(), sv.unique("id")]},
    ensures=[_.amount >= 0, _.amount.notnull(), sv.unique("id")],
)
def paid(orders):
    return orders.filter(orders.amount.notnull())


@sv.transform(
    requires={"t": [_.amount >= 0, _.amount.notnull(), sv.unique("id")]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), sv.unique("id")],
)
def doubled(t):
    return t.select(t.id, t.customer, doubled=t.amount * 2)


def sources(report):
    return {(p.table, p.condition): p.source for p in report}


# -- Step 1: the Change Data Feed as a change source --------------------------


@pytest.mark.parametrize("engine", ["datafusion", "polars", "duckdb"])
def test_refresh_applies_cdf(tmp_path, engine: Engine):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    pipe = sv.Pipeline(sv.connect(), engine)
    orders = pipe.source("orders", src)
    big = pipe.view("big", doubled(paid(orders)))
    assert big.versions == {"orders": 1}
    dt = DeltaTable(src.uri)
    write_deltalake(dt, orders_table([(3, "cy", 1)]), mode="append")
    dt.update(updates={"amount": "amount + 1"}, predicate="id = 1")
    dt.delete("id = 2")
    report = pipe.refresh()
    assert big.rows() == [(1, "ada", 12), (3, "cy", 2)]
    assert big.rows() == big.recompute()
    assert big.versions == {"orders": 4}
    [s] = report.sources
    assert (s.start, s.end, s.mode) == (1, 4, "change feed")
    assert (s.inserts, s.deletes) == (2, 2)
    assert "Δ trusted as coming from Delta CDF v1→v4" in str(report)
    assert "view big: orders@v4" in str(report)


def test_refresh_without_new_version_is_a_no_op(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    pipe = sv.Pipeline(sv.connect())
    pipe.view("big", doubled(paid(pipe.source("orders", src))))
    report = pipe.refresh()
    assert str(report.sources[0]) == "orders@v1: no new version"


def test_a_failed_refresh_changes_nothing_and_a_retry_applies_once(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    # A duplicate key: Delta does not enforce keys, the pipeline does.
    write_deltalake(src.uri, orders_table([(1, "eve", 3)]), mode="append")
    with pytest.raises(sv.PreconditionError, match="unique"):
        pipe.refresh()
    assert pipe.versions == {"orders": 1}
    assert big.rows() == [(1, "ada", 10)]
    DeltaTable(src.uri).delete("customer = 'eve'")
    write_deltalake(src.uri, orders_table([(2, "bob", 1)]), mode="append")
    report = pipe.refresh()
    # The CDF from v1 holds eve's insert and delete; they cancel out.
    assert (report.sources[0].inserts, report.sources[0].deletes) == (1, 0)
    assert big.rows() == [(1, "ada", 10), (2, "bob", 2)]
    assert pipe.refresh().sources[0].mode == "unchanged"
    assert big.rows() == [(1, "ada", 10), (2, "bob", 2)]


def test_no_cdf_recomputes_and_says_so(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)], cdf=False)
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    write_deltalake(src.uri, orders_table([(2, "bob", 1)]), mode="append")
    report = pipe.refresh()
    [s] = report.sources
    assert s.mode == "recomputed"
    assert report.recomputed == ["orders"]
    assert "Delta CDF v1→v2 unavailable" in s.detail
    assert "recomputed from scratch" in str(report)
    assert big.rows() == [(1, "ada", 10), (2, "bob", 2)]


def test_vacuumed_history_recomputes(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="overwrite")
    DeltaTable(src.uri).vacuum(retention_hours=0, enforce_retention_duration=False, dry_run=False)
    report = pipe.refresh()
    assert report.sources[0].mode == "recomputed"
    assert big.rows() == [(3, "cy", 2)]


def test_audit_compares_with_the_snapshot(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    write_deltalake(src.uri, orders_table([(2, "bob", 1)]), mode="append")
    report = pipe.refresh(audit=True)
    assert report.audited and "audit:" in str(report)
    assert big.rows() == big.recompute()


def test_audit_catches_a_wrong_feed(tmp_path, monkeypatch):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    write_deltalake(src.uri, orders_table([(2, "bob", 1)]), mode="append")
    real = DeltaSource.changes

    def lossy(self, since):
        batch = real(self, since)
        batch.changes = sv.Changes()
        return batch

    monkeypatch.setattr(DeltaSource, "changes", lossy)
    with pytest.raises(AuditError, match="nothing was applied"):
        pipe.refresh(audit=True)
    assert pipe.versions == {"orders": 1} and big.rows() == [(1, "ada", 10)]


def test_source_tables_change_only_through_refresh(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    pipe = sv.Pipeline(sv.connect())
    pipe.view("big", doubled(paid(pipe.source("orders", src))))
    with pytest.raises(ValueError, match="refresh"):
        pipe.apply({"orders": sv.Changes(inserts=[(2, "bob", 1)])})


def test_views_over_views_record_source_versions(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    top = pipe.view("top", big.table.filter(big.table.doubled > 4))
    write_deltalake(src.uri, orders_table([(2, "bob", 9)]), mode="append")
    report = pipe.refresh()
    assert top.versions == {"orders": 2}
    assert report.versions == {"big": {"orders": 2}, "top": {"orders": 2}}
    assert top.rows() == [(1, "ada", 10), (2, "bob", 18)]


def test_timestamps_and_nulls_round_trip(tmp_path):
    schema = pa.schema([pa.field("k", pa.int64(), nullable=False), pa.field("ts", pa.timestamp("us"))])
    t1 = datetime(2024, 1, 1, 0, 0, 0, 123456)
    write_deltalake(
        tmp_path / "ev",
        pa.Table.from_pylist([{"k": 1, "ts": t1}], schema=schema),
        configuration={"delta.enableChangeDataFeed": "true"},
    )
    pipe = sv.Pipeline(sv.connect())
    ev = pipe.source("ev", DeltaSource(str(tmp_path / "ev")))
    view = pipe.view("v", ev.filter(ev.k > 0))
    write_deltalake(
        tmp_path / "ev", pa.Table.from_pylist([{"k": 2, "ts": None}], schema=schema), mode="append"
    )
    pipe.refresh()
    assert view.rows() == view.recompute() == [(1, t1), (2, None)]
    assert ibis is not None and SCHEMA and ON_DATA and DeltaSink

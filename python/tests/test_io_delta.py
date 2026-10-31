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
    schema = pa.schema(
        [pa.field("k", pa.int64(), nullable=False), pa.field("ts", pa.timestamp("us"))]
    )
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


# -- Step 2: preconditions from table metadata --------------------------------


@sv.transform(
    requires={
        "orders": [
            _.id.notnull(),
            _.amount >= 0,
            _.amount <= 100,
            _.customer.notnull(),
            _.customer != "eve",
            sv.unique("id"),
        ]
    },
    ensures=[_.amount >= 0],
)
def checked(orders):
    return orders.select(orders.id, orders.amount)


def test_preconditions_come_from_metadata(tmp_path):
    src = make_orders(
        tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)], constraints={"pos": "amount >= 0"}
    )
    pipe = sv.Pipeline(sv.connect())
    orders = pipe.source("orders", src)
    checked(orders)
    assert sources(checked.last_preconditions) == {
        ("orders", "_.id.notnull()"): SCHEMA,
        ("orders", "(_.amount >= 0)"): "Delta constraint",
        ("orders", "(_.amount <= 100)"): "file stats @v2",
        # NULL counts are exact, even for strings ...
        ("orders", "_.customer.notnull()"): "file stats @v2",
        # ... but string bounds are not used.
        ("orders", "(_.customer != 'eve')"): ON_DATA,
        # Neither format enforces keys.
        ("orders", "unique(id)"): ON_DATA,
    }
    view = pipe.view("v", checked(orders))
    assert sources(pipe.preconditions)[("orders", "(_.amount <= 100)")] == "file stats @v2"
    assert "orders: (_.amount <= 100) (file stats @v2)" in [str(p) for p in pipe.preconditions]
    # A batch is discharged from the statistics of the files it added.
    write_deltalake(src.uri, orders_table([(3, "cy", 50)]), mode="append")
    report = pipe.refresh()
    found = sources(report.preconditions)
    assert found[("orders", "(_.amount <= 100)")] == "file stats @v3 (new files)"
    assert found[("orders", "(_.amount >= 0)")] == "Delta constraint"
    assert found[("orders", "unique(id)")] == ON_DATA
    assert "requires orders: (_.amount <= 100) (file stats @v3 (new files))" in str(report)
    # Statistics that do not bound the batch leave it to the data.
    write_deltalake(src.uri, orders_table([(4, "dan", 500)]), mode="append")
    with pytest.raises(sv.PreconditionError, match=r"inserted row\(s\) of orders violate"):
        pipe.refresh()
    assert view.versions == {"orders": 3}


def test_missing_statistics_are_unknown(tmp_path):
    path = tmp_path / "orders"
    write_deltalake(
        path,
        orders_table([(1, "ada", 5)]),
        configuration={"delta.dataSkippingNumIndexedCols": "0"},
    )
    checked(sv.Pipeline(sv.connect()).source("orders", DeltaSource(str(path))))
    found = sources(checked.last_preconditions)
    assert found[("orders", "(_.amount <= 100)")] == ON_DATA
    assert found[("orders", "_.id.notnull()")] == SCHEMA


def test_one_file_without_statistics_makes_a_column_unknown(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    DeltaTable(src.uri).alter.set_table_properties({"delta.dataSkippingNumIndexedCols": "0"})
    write_deltalake(src.uri, orders_table([(2, "bob", 6)]), mode="append")
    checked(sv.Pipeline(sv.connect()).source("orders", src))
    assert sources(checked.last_preconditions)[("orders", "(_.amount <= 100)")] == ON_DATA


def test_truncated_timestamp_statistics_are_widened(tmp_path):
    schema = pa.schema([pa.field("ts", pa.timestamp("us"), nullable=False)])
    t1 = datetime(2024, 1, 1, 0, 0, 0, 123456)
    write_deltalake(tmp_path / "ev", pa.Table.from_pylist([{"ts": t1}], schema=schema))
    ev = sv.Pipeline(sv.connect()).source("ev", DeltaSource(str(tmp_path / "ev")))

    @sv.transform(
        requires={
            "t": [
                _.ts >= datetime(2024, 1, 1),
                _.ts <= datetime(2024, 1, 1, 0, 0, 0, 124000),
                _.ts <= t1,
            ]
        }
    )
    def f(t):
        return t

    f(ev)
    # Delta keeps the maximum as ...00.123000; the true maximum is up to
    # 999 µs later, so only the weaker bound follows from the statistics.
    assert [p.source for p in f.last_preconditions] == ["file stats @v0", "file stats @v0", ON_DATA]


def test_tables_without_metadata_are_checked_on_data():
    con = sv.connect()
    sv.create_table(
        con,
        "orders",
        ibis.schema({"id": "!int64", "customer": "string", "amount": "int64"}),
        [(1, "ada", 5)],
    )
    checked(con.table("orders"))
    assert set(sources(checked.last_preconditions).values()) == {ON_DATA}


# -- Step 3: a Delta sink that carries the contract ---------------------------


def delta_rows(uri):
    t = pa.table(DeltaTable(uri).to_pyarrow_table())
    return sorted((tuple(r.values()) for r in t.to_pylist()), key=repr)


def job1(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    return src, pipe, big, DeltaSink(str(tmp_path / "big"), big)


def test_sink_writes_contract_and_changes(tmp_path):
    src, pipe, big, sink = job1(tmp_path)
    first = sink.write()
    assert first.mode == "created"
    assert delta_rows(sink.uri) == big.rows()
    out = DeltaTable(sink.uri)
    fields = {f.name: f.nullable for f in pa.schema(out.schema().to_arrow())}
    assert fields == {"id": True, "customer": True, "doubled": False}
    assert out.metadata().configuration["delta.constraints.sverify_1"] == "doubled >= 0"
    assert out.transaction_version("sverify:big") == 1
    contract = DeltaSource(sink.uri).contract()
    assert contract is not None
    assert contract.sources == {"orders": 1} and contract.unique == [["id"]]
    assert contract.plan == first.contract.plan and len(contract.plan) == 64
    # A change to the source becomes one MERGE commit on the sink.
    dt = DeltaTable(src.uri)
    dt.update(updates={"amount": "amount + 1"}, predicate="id = 1")
    write_deltalake(dt, orders_table([(3, "cy", 0)]), mode="append")
    pipe.refresh()
    before = DeltaTable(sink.uri).version()
    second = sink.write()
    assert second.mode == "merge" and second.version == before + 1
    assert (second.inserted, second.deleted) == (2, 1)
    assert delta_rows(sink.uri) == big.rows() == [(1, "ada", 12), (2, "bob", 14), (3, "cy", 0)]
    later = DeltaSource(sink.uri).contract()
    assert later is not None and later.sources == {"orders": 3}
    assert DeltaTable(sink.uri).transaction_version("sverify:big") == 3


def test_sink_writes_exactly_once(tmp_path):
    src, pipe, big, sink = job1(tmp_path)
    sink.write()
    version = DeltaTable(sink.uri).version()
    assert sink.write().mode == "skipped"
    # A restarted job at the same source versions finds its commit.
    _, _, _, again = job1_restart(src, tmp_path)
    assert again.write().mode == "skipped"
    assert DeltaTable(sink.uri).version() == version
    # At a later version, a new sink replaces the table's contents.
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="append")
    _, _, big2, later = job1_restart(src, tmp_path)
    assert later.write().mode == "overwrite"
    assert delta_rows(sink.uri) == big2.rows()


def job1_restart(src, tmp_path):
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    return src, pipe, big, DeltaSink(str(tmp_path / "big"), big)


def test_sink_keeps_multiplicities_and_nulls(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "ada", 5), (3, None, 1)])
    pipe = sv.Pipeline(sv.connect())
    orders = pipe.source("orders", src)
    names = pipe.view("names", orders.select(orders.customer, orders.amount))
    sink = DeltaSink(str(tmp_path / "names"), names)
    sink.write()
    DeltaTable(src.uri).delete("id = 1")
    write_deltalake(src.uri, orders_table([(4, None, 1), (5, "ada", 5)]), mode="append")
    pipe.refresh()
    sink.write()
    assert delta_rows(sink.uri) == sorted(names.rows(), key=repr)
    assert len(names.rows()) == 4


def test_contracts_travel_between_jobs(tmp_path):
    src, pipe, big, sink = job1(tmp_path)
    sink.write()

    @sv.transform(
        requires={"t": [_.doubled >= 0, _.doubled.notnull(), sv.unique("id")]},
        ensures=[_.half >= 0],
    )
    def halved(t):
        return t.select(t.id, half=t.doubled // 2)

    # Job 2 reads job 1's output; its preconditions come from job 1's contract.
    pipe2 = sv.Pipeline(sv.connect())
    big_in = pipe2.source("big", DeltaSource(sink.uri))
    halves = pipe2.view("halves", halved(big_in))
    assert sources(pipe2.preconditions) == {
        ("big", "(_.doubled >= 0)"): "Delta constraint",
        ("big", "_.doubled.notnull()"): SCHEMA,
        ("big", "unique(id)"): ON_DATA,
    }
    # Job 1 moves on; job 2 follows the sink's own change feed.
    write_deltalake(src.uri, orders_table([(3, "cy", 4)]), mode="append")
    pipe.refresh()
    sink.write()
    report = pipe2.refresh()
    assert report.sources[0].mode == "change feed"
    assert halves.rows() == halves.recompute() == [(1, 5), (2, 7), (3, 4)]
    assert sources(report.preconditions)[("big", "(_.doubled >= 0)")] == "Delta constraint"


def test_sink_needs_source_versions(tmp_path):
    con = sv.connect()
    sv.create_table(con, "orders", ibis.schema({"id": "int64"}), [(1,)])
    view = sv.IncrementalView(con, con.table("orders"), "v")
    with pytest.raises(ValueError, match="without a source"):
        DeltaSink(str(tmp_path / "v"), view).write()

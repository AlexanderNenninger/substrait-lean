"""Pruning data files by their statistics (#81): string bounds cut to
prefixes, NaN in double bounds, and `IcebergSource(where=...)`.

The criterion is proved in `SubstraitLean/Pruning.lean`; `str_may_true`
mirrors `StrStats.mayTrue`."""

import math
import warnings
from datetime import datetime

import pyarrow as pa
import pyarrow.compute as pc
import pyarrow.dataset as ds
import pytest
import sqlglot as sg
from deltalake import write_deltalake
from hypothesis import given
from hypothesis import strategies as st
from ibis import _
from pyiceberg.catalog.sql import SqlCatalog

import sverify as sv
from _pipelines import rows
from sverify.incremental import arrow_rows
from sverify.io import DeltaSource, IcebergSource
from sverify.io._common import str_may_true
from sverify.io.iceberg import _live_files

# -- The string criterion -------------------------------------------------------


def may(where: str, lo: str | None, hi: str | None) -> bool:
    return str_may_true(sg.parse_one(where, read="duckdb"), {"s": (lo, hi)})


def test_string_bounds_as_lean_checks_them():
    # The `#guard`s of `SubstraitLean/Pruning.lean`.
    assert may("s >= 'apple'", None, "app")
    assert not may("s >= 'apq'", None, "app")
    assert not may("s = 'b'", "c", "d")
    assert not may("s < 'c'", "c", "d")
    assert may("s <= 'c'", "c", "d")
    # Literals on the left, AND, OR, IN, and what the criterion leaves alone.
    assert not may("'c' > s", "c", "d")
    assert not may("s >= 'c' AND s = 'b'", "c", "d")
    assert may("s = 'b' OR s = 'cc'", "c", "d")
    assert not may("s IN ('a', 'b')", "c", "d")
    assert may("s IN ('a', 'c')", "c", "d")
    assert may("upper(s) = 'B'", "c", "d")
    assert may("t = 'b'", "c", "d")


def truncated_hi(m: str, n: int, increment: bool) -> str:
    """A maximum as writers keep it: `m` cut to `n` characters, and, as
    Iceberg does, with the last character incremented."""
    if len(m) <= n:
        return m
    if not increment:
        return m[:n]
    p = m[:n]
    while p and ord(p[-1]) == 0x10FFFF:
        p = p[:-1]
    return p[:-1] + chr(ord(p[-1]) + 1) if p else m


ALPHABET = st.sampled_from(["a", "b", "c", "é", "z", "\U0001f600"])
STRINGS = st.lists(ALPHABET, max_size=6).map("".join)


@given(
    values=st.lists(STRINGS, min_size=1, max_size=5),
    k=STRINGS,
    n=st.integers(0, 4),
    increment=st.booleans(),
    op=st.sampled_from(["=", "<", "<=", ">", ">="]),
    flip=st.booleans(),
)
def test_truncated_bounds_never_skip_a_match(values, k, n, increment, op, flip):
    """`strPrune_sound` on samples: whenever a value makes the comparison
    TRUE, the bounds a writer keeps (prefixes) allow it."""
    lo, hi = min(values)[:n], truncated_hi(max(values), n, increment)
    lit = "'" + k.replace("'", "''") + "'"
    swapped = {"<": ">", "<=": ">=", ">": "<", ">=": "<=", "=": "="}
    where = f"{lit} {swapped[op]} s" if flip else f"s {op} {lit}"
    holds = {
        "=": str.__eq__,
        "<": str.__lt__,
        "<=": str.__le__,
        ">": str.__gt__,
        ">=": str.__ge__,
    }[op]
    if any(holds(v, k) for v in values):
        assert may(where, lo, hi)


# -- Delta ----------------------------------------------------------------------


def test_delta_string_bounds_skip_files(tmp_path):
    path = tmp_path / "people"
    write_deltalake(path, pa.table({"id": [1, 2], "name": ["ada", "bob"]}))
    write_deltalake(path, pa.table({"id": [3, 4], "name": ["cy", "dan"]}), mode="append")
    src = DeltaSource(str(path), where="name >= 'c'")
    snap = src.snapshot()
    assert len(src.skipped) == 1
    assert sorted(arrow_rows(snap.table)) == [(3, "cy"), (4, "dan")]


def test_delta_nan_keeps_a_file_whose_maximum_is_below(tmp_path):
    # NaN > 100 is TRUE, and writers leave NaN out of the maximum: a file
    # with maximum 1.0 may still hold a row that passes.
    path = tmp_path / "readings"
    write_deltalake(path, pa.table({"x": [1.0, math.nan]}))
    write_deltalake(path, pa.table({"x": [-5.0, 0.5]}), mode="append")
    src = DeltaSource(str(path), where="x > 100")
    snap = src.snapshot()
    assert src.skipped == []  # Delta counts no NaN: no maximum is used
    [(x,)] = arrow_rows(snap.table)
    assert math.isnan(x)


# -- Iceberg --------------------------------------------------------------------


@pytest.fixture
def catalog(tmp_path):
    warnings.filterwarnings("ignore", module="pyiceberg")
    cat = SqlCatalog("test", uri=f"sqlite:///{tmp_path}/catalog.db", warehouse=f"file://{tmp_path}")
    cat.create_namespace("db")
    return cat


ORDERS = pa.schema([pa.field("id", pa.int64()), pa.field("amount", pa.int64())])


def orders(rs):
    return pa.Table.from_pylist([{"id": i, "amount": a} for i, a in rs], schema=ORDERS)


def test_iceberg_where_skips_files_the_reader_would_scan(catalog):
    t = catalog.create_table("db.orders", schema=ORDERS)
    t.append(orders([(1, 5), (2, 50)]))
    t.append(orders([(3, 60), (4, 80)]))
    src = IcebergSource(catalog, "db.orders", where="amount * 2 > 100")
    snap = src.snapshot()
    # Lean proves amount * 2 > 100 is not TRUE in the file with amounts in [5, 50].
    assert len(src.skipped) == 1
    assert sorted(arrow_rows(snap.table)) == [(3, 60), (4, 80)]
    assert ("amount * 2 > 100", "source filter") in [(f.condition, f.source) for f in snap.facts]
    # pyarrow's statistics pushdown keeps both files for this filter.
    files = [
        e["data_file"]["file_path"].removeprefix("file://")
        for e in _live_files(t, t.current_snapshot())
    ]
    dataset = ds.dataset(files, format="parquet")
    expr = pc.field("amount") * 2 > 100
    assert len([f for f in dataset.get_fragments() if f.subset(filter=expr).row_groups]) == 2
    # DuckDB reads only the files kept.
    native = src._native()
    assert native is not None and len(native.scan.files) == 1
    assert sorted(arrow_rows(native.scan.to_arrow())) == [(3, 60), (4, 80)]
    # As a node's source: an appended file of small amounts is not read, and
    # the change is filtered.
    node = src.pipe(lambda o: o.select(o.id, o.amount))
    node.refresh()
    t = catalog.load_table("db.orders")
    t.append(orders([(5, 10), (6, 20)]))
    t.append(orders([(7, 10), (8, 70)]))
    node.refresh(audit=True)
    assert rows(node) == [(3, 60), (4, 80), (8, 70)]


def test_iceberg_truncated_string_bounds(catalog):
    schema = pa.schema([pa.field("id", pa.int64()), pa.field("name", pa.string())])
    t = catalog.create_table("db.people", schema=schema)
    long = "x" * 20
    t.append(pa.table({"id": [1, 2], "name": ["a" + long, "b" + long]}, schema=schema))
    t.append(pa.table({"id": [3, 4], "name": ["c" + long, "d" + long]}, schema=schema))
    # pyiceberg keeps 16 characters of each bound.
    bounds = [
        e["readable_metrics"]["name"]["upper_bound"] for e in _live_files(t, t.current_snapshot())
    ]
    assert all(len(b) <= 16 for b in bounds)
    src = IcebergSource(catalog, "db.people", where=f"name = 'd{long}'")
    snap = src.snapshot()
    assert len(src.skipped) == 1
    assert arrow_rows(snap.table) == [(4, "d" + long)]
    # Above the first file's names, but within its maximum cut to 16
    # characters: the file is read.
    src = IcebergSource(catalog, "db.people", where=f"name >= 'b{long}z'")
    assert sorted(arrow_rows(src.snapshot().table)) == [(3, "c" + long), (4, "d" + long)]
    assert src.skipped == []


def test_iceberg_nan_is_never_pruned(catalog):
    schema = pa.schema([pa.field("x", pa.float64())])
    t = catalog.create_table("db.readings", schema=schema)
    t.append(pa.table({"x": [1.0, math.nan]}, schema=schema))
    t.append(pa.table({"x": [200.0, 300.0]}, schema=schema))
    src = IcebergSource(catalog, "db.readings", where="x > 100")
    got = sorted(arrow_rows(src.snapshot().table), key=lambda r: (math.isnan(r[0]), r[0]))
    assert got[:2] == [(200.0,), (300.0,)] and math.isnan(got[2][0])


# -- Implied predicates -----------------------------------------------------------

T0 = datetime(2025, 6, 1)
T1 = datetime(2026, 3, 1)


@sv.transform(requires={"customers": [_.since >= datetime(2026, 1, 1)]})
def since_joining(orders, customers):
    joined = orders.join(customers, orders.cid == customers.cid)
    return joined.filter(orders.ts >= customers.since).select(orders.id, orders.amount)


def lake(tmp_path):
    orders, customers = tmp_path / "orders", tmp_path / "customers"
    order_rows = pa.schema(
        [
            ("id", pa.int64()),
            ("cid", pa.int64()),
            ("ts", pa.timestamp("us")),
            ("amount", pa.int64()),
        ]
    )

    def order(rs):
        return pa.Table.from_pylist(
            [dict(zip(order_rows.names, r, strict=True)) for r in rs], schema=order_rows
        )

    write_deltalake(
        orders,
        order([(1, 1, T0, 10), (2, 2, T0, 20)]),
        configuration={"delta.enableChangeDataFeed": "true"},
    )
    write_deltalake(orders, order([(3, 1, T1, 30), (4, 2, T1, 40)]), mode="append")
    write_deltalake(
        customers,
        pa.table({"cid": [1, 2], "since": [datetime(2026, 2, 1), datetime(2026, 4, 1)]}),
    )
    return orders, customers, order


def test_a_predicate_the_view_implies_prunes_files(tmp_path):
    orders_path, customers_path, order = lake(tmp_path)
    node = since_joining(DeltaSource(str(orders_path)), DeltaSource(str(customers_path)))
    node.refresh(audit=True)
    # The query states no condition on orders.ts alone, so a reader's
    # pushdown has nothing to prune with. With `since >= 2026-01-01` on
    # every customer, only orders from 2026 on can join: Lean derives it
    # (`Rel.need_eval`) and the source skips the file of 2025 orders.
    src = node._stage.pipe.sources["orders"]
    assert src.implied == "(\"ts\" >= TIMESTAMP '2026-01-01 00:00:00.000000')"
    assert len(src.skipped) == 1
    assert rows(node) == [(3, 30)]
    # Changes are filtered the same way, and the result stays that of the
    # whole table.
    write_deltalake(
        orders_path, order([(5, 1, T0, 50), (6, 2, datetime(2026, 5, 1), 60)]), mode="append"
    )
    node.refresh(audit=True)
    assert rows(node) == [(3, 30), (6, 60)]


def test_no_implied_predicate_through_a_left_join(tmp_path):
    orders_path, customers_path, _order = lake(tmp_path)

    @sv.transform(requires={"customers": [_.since >= datetime(2026, 1, 1)]})
    def kept(orders, customers):
        joined = orders.left_join(customers, orders.cid == customers.cid)
        return joined.select(orders.id, customers.since)

    node = kept(DeltaSource(str(orders_path)), DeltaSource(str(customers_path)))
    node.refresh()
    assert node._stage.pipe.sources["orders"].implied is None
    assert len(rows(node)) == 4


def test_an_iceberg_source_reads_what_the_view_implies(catalog):
    t = catalog.create_table("db.orders", schema=ORDERS)
    t.append(orders([(1, 5), (2, 6)]))
    t.append(orders([(3, 60), (4, 80)]))
    limits = catalog.create_table("db.limits", schema=pa.schema([("id", pa.int64())]))
    limits.append(pa.table({"id": [3, 4]}))

    @sv.transform(requires={"limits": [_.id >= 3]})
    def matched(o, limits):
        return o.join(limits, o.id == limits.id).select(o.id, o.amount)

    node = matched(IcebergSource(catalog, "db.orders"), IcebergSource(catalog, "db.limits"))
    node.refresh(audit=True)
    src = node._stage.pipe.sources["orders"]
    assert src.implied == '("id" >= 3)'
    assert len(src.skipped) == 1
    assert rows(node) == [(3, 60), (4, 80)]

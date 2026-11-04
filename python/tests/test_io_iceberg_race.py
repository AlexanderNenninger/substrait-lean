"""Two processes refreshing the same `IcebergSink` (#534, the Iceberg case
of #517): A reads what the sink committed, B commits, then A writes. A's
commit must fail, with an error naming the sink, and A's next refresh must
recover. On DuckDB the sink commits the files DuckDB wrote
(`_write_native`); on Polars it writes Arrow."""

import warnings

import pyarrow as pa
import pytest
from ibis import _
from pyiceberg.catalog.sql import SqlCatalog

import sverify as sv
from sverify.errors import ConcurrentWriteError
from sverify.io import IcebergSink, IcebergSource
from sverify.io import iceberg as iceberg_io

SCHEMA = pa.schema([("id", pa.int64()), ("amount", pa.int64())])
ENGINES = ["duckdb", "polars"]
SINK = "db.paid"

@sv.transform(requires={"orders": [_.amount >= 0]})
def paid(orders):
    return orders.filter(orders.amount > 0)


def append(catalog, ids: list[int]) -> None:
    rows = pa.table({"id": ids, "amount": [5] * len(ids)}, schema=SCHEMA)
    catalog.load_table("db.orders").append(rows)


def ids(catalog) -> list[int]:
    return sorted(r["id"] for r in catalog.load_table(SINK).scan().to_arrow().to_pylist())


def epoch(catalog) -> int | None:
    c = IcebergSink(catalog, SINK).committed()
    return None if c is None else c.epoch


@pytest.fixture
def catalog(tmp_path):
    warnings.filterwarnings("ignore", module="pyiceberg")
    cat = SqlCatalog("race", uri=f"sqlite:///{tmp_path}/catalog.db", warehouse=f"file://{tmp_path}")
    cat.create_namespace("db")
    cat.create_table("db.orders", schema=SCHEMA)
    append(cat, [1, 2])
    return cat


@pytest.fixture
def jobs(catalog):
    """Two jobs storing `paid` in the same sink, both at orders@v1."""

    def job():
        return paid(IcebergSource(catalog, "db.orders", name="orders")).write(
            IcebergSink(catalog, SINK)
        )

    return job(), job()


def hold(monkeypatch, a, method: str, then) -> None:
    """Run `then` once, when `a`'s sink is past `IcebergSink.<method>`: the
    hook stands in for the scheduler pausing process A there."""
    original = getattr(IcebergSink, method)

    def held(self, *args):
        out = original(self, *args)
        if self is a.sink:
            monkeypatch.setattr(IcebergSink, method, original)
            then()
        return out

    monkeypatch.setattr(IcebergSink, method, held)


@pytest.mark.parametrize("engine", ENGINES)
def test_the_second_writer_of_an_epoch_fails(catalog, jobs, monkeypatch, engine):
    a, b = jobs
    a.refresh(engine=engine)
    b.refresh(engine=engine)
    append(catalog, [3])
    # A is held after reading the sink's last snapshot.
    hold(monkeypatch, a, "committed", lambda: b.refresh(engine=engine))
    with pytest.raises(ConcurrentWriteError, match=rf"{SINK}.*sverify:paid.*epoch 2"):
        a.refresh(engine=engine)
    assert ids(catalog) == [1, 2, 3]
    assert epoch(catalog) == 2
    # A recovers: the sink holds this state, and later changes write on it.
    assert a.refresh(engine=engine).writes[0].mode == "skipped"
    append(catalog, [4])
    a.refresh(engine=engine)
    assert ids(catalog) == [1, 2, 3, 4]
    b.refresh(engine=engine)
    assert ids(catalog) == [1, 2, 3, 4]


@pytest.mark.parametrize("engine", ENGINES)
def test_a_commit_pyiceberg_would_retry(catalog, jobs, monkeypatch, engine):
    """B commits after A staged its snapshot: pyiceberg's commit fails on
    the stale parent and retries on top of B's snapshot, which must not
    land A's change a second time."""
    a, b = jobs
    a.refresh(engine=engine)
    b.refresh(engine=engine)
    append(catalog, [3])
    original = iceberg_io._commit_rows

    def held(*args, **kw):
        monkeypatch.setattr(iceberg_io, "_commit_rows", original)
        original(*args, **kw)
        b.refresh(engine=engine)

    monkeypatch.setattr(iceberg_io, "_commit_rows", held)
    with pytest.raises(ConcurrentWriteError):
        a.refresh(engine=engine)
    assert ids(catalog) == [1, 2, 3]
    assert a.refresh(engine=engine).writes[0].mode == "skipped"


@pytest.mark.parametrize("engine", ENGINES)
def test_an_older_write_does_not_land_on_a_newer_state(catalog, jobs, monkeypatch, engine):
    a, b = jobs
    a.refresh(engine=engine)
    b.refresh(engine=engine)
    append(catalog, [3])

    def b_is_ahead():
        append(catalog, [4])
        b.refresh(engine=engine)  # epoch 3, A writes epoch 2

    hold(monkeypatch, a, "committed", b_is_ahead)
    with pytest.raises(ConcurrentWriteError):
        a.refresh(engine=engine)
    assert ids(catalog) == [1, 2, 3, 4]
    # A catches up to B's state, and writes on from it.
    a.refresh(engine=engine)
    append(catalog, [5])
    a.refresh(engine=engine)
    assert ids(catalog) == [1, 2, 3, 4, 5]


@pytest.mark.parametrize("engine", ENGINES)
def test_two_writers_creating_the_table(catalog, jobs, monkeypatch, engine):
    a, b = jobs
    hold(monkeypatch, a, "committed", lambda: b.refresh(engine=engine))
    with pytest.raises(ConcurrentWriteError):
        a.refresh(engine=engine)
    assert ids(catalog) == [1, 2]
    assert a.refresh(engine=engine).writes[0].mode == "skipped"

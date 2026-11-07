"""Two processes refreshing the same `DeltaSink` (#517): A reads what the sink
committed, B commits, then A writes. A's commit must fail, with an error
naming the sink, and A's next refresh must recover. On DuckDB the sink
commits the files DuckDB wrote (`_write_native`); on Polars it MERGEs."""

import pyarrow as pa
import pytest
from deltalake import DeltaTable, write_deltalake
from ibis import _

import sverify as sv
from sverify.errors import ConcurrentWriteError
from sverify.io import DeltaSink, DeltaSource

SCHEMA = pa.schema([("id", pa.int64()), ("amount", pa.int64())])
ENGINES = ["duckdb", "polars"]


@sv.transform(requires={"orders": [_.amount >= 0]})
def paid(orders):
    return orders.filter(orders.amount > 0)


def append(src: str, ids: list[int]) -> None:
    write_deltalake(src, pa.table({"id": ids, "amount": [5] * len(ids)}), mode="append")


def ids(uri: str) -> list[int]:
    return sorted(r["id"] for r in DeltaTable(uri).to_pyarrow_table().to_pylist())


@pytest.fixture
def jobs(tmp_path):
    """Two jobs storing `paid` in the same sink, both at orders@v1."""
    src, sink = str(tmp_path / "orders"), str(tmp_path / "paid")
    DeltaTable.create(src, SCHEMA, configuration={"delta.enableChangeDataFeed": "true"})
    append(src, [1, 2])

    def job():
        return paid(DeltaSource(src)).write(DeltaSink(sink))

    return src, sink, job(), job()


def hold(monkeypatch, a, method: str, then) -> None:
    """Run `then` once, when `a`'s sink is past `DeltaSink.<method>`: the
    hook stands in for the scheduler pausing process A there."""
    original = getattr(DeltaSink, method)

    def held(self, *args):
        out = original(self, *args)
        if self is a.sink:
            monkeypatch.setattr(DeltaSink, method, original)
            then()
        return out

    monkeypatch.setattr(DeltaSink, method, held)


@pytest.mark.parametrize("engine", ENGINES)
def test_the_second_writer_of_an_epoch_fails(jobs, monkeypatch, engine):
    src, sink, a, b = jobs
    a.refresh(engine=engine)
    b.refresh(engine=engine)
    append(src, [3])
    # The issue's repro: A is held after reading the sink's last transaction.
    hold(monkeypatch, a, "contract", lambda: b.refresh(engine=engine))
    with pytest.raises(ConcurrentWriteError, match=rf"{sink}.*sverify:paid.*epoch 2"):
        a.refresh(engine=engine)
    assert ids(sink) == [1, 2, 3]
    assert DeltaTable(sink).transaction_version("sverify:paid") == 2
    # A recovers: the sink holds this state, and later changes merge on it.
    assert a.refresh(engine=engine).writes[0].mode == "skipped"
    append(src, [4])
    a.refresh(engine=engine)
    assert ids(sink) == [1, 2, 3, 4]
    b.refresh(engine=engine)
    assert ids(sink) == [1, 2, 3, 4]


@pytest.mark.parametrize("engine", ENGINES)
def test_a_commit_delta_rs_rejects(jobs, monkeypatch, engine):
    """B commits after A's last check: delta-rs's conflict check on A's
    snapshot rejects A's commit (`CommitFailedError`)."""
    src, sink, a, b = jobs
    a.refresh(engine=engine)
    b.refresh(engine=engine)
    append(src, [3])

    def b_commits():
        b.refresh(engine=engine)
        monkeypatch.setattr(DeltaSink, "_check", lambda *args: None)

    hold(monkeypatch, a, "_check", b_commits)
    with pytest.raises(ConcurrentWriteError, match="delta-rs"):
        a.refresh(engine=engine)
    monkeypatch.undo()
    assert ids(sink) == [1, 2, 3]
    assert a.refresh(engine=engine).writes[0].mode == "skipped"


@pytest.mark.parametrize("engine", ENGINES)
def test_an_older_write_does_not_land_on_a_newer_state(jobs, monkeypatch, engine):
    src, sink, a, b = jobs
    a.refresh(engine=engine)
    b.refresh(engine=engine)
    append(src, [3])

    def b_is_ahead():
        append(src, [4])
        b.refresh(engine=engine)  # epoch 3, A writes epoch 2

    hold(monkeypatch, a, "contract", b_is_ahead)
    with pytest.raises(ConcurrentWriteError):
        a.refresh(engine=engine)
    assert ids(sink) == [1, 2, 3, 4]
    # A catches up to B's state, and writes on from it.
    a.refresh(engine=engine)
    append(src, [5])
    a.refresh(engine=engine)
    assert ids(sink) == [1, 2, 3, 4, 5]


@pytest.mark.parametrize("engine", ENGINES)
def test_two_writers_creating_the_table(jobs, monkeypatch, engine):
    _src, sink, a, b = jobs
    hold(monkeypatch, a, "contract", lambda: b.refresh(engine=engine))
    with pytest.raises(ConcurrentWriteError):
        a.refresh(engine=engine)
    assert ids(sink) == [1, 2]
    assert a.refresh(engine=engine).writes[0].mode == "skipped"


@sv.transform(requires={"other": [_.amount >= 0]})
def paid_other(other):
    """Another plan for the same sink, as a deploy brings it."""
    return other.filter(other.amount > 1)


@pytest.mark.parametrize("engine", ENGINES)
def test_another_plans_commit_at_the_same_epoch_fails_the_write(
    jobs, tmp_path, monkeypatch, engine
):
    """#964 (the TLA+ model's `today-aba` trace): A read epoch 1; another
    plan replaces the rows at epoch 1 too. The epoch's value is the same, but
    A's change must not land on the other plan's rows."""
    src, sink, a, _b = jobs
    a.refresh(engine=engine)
    other = str(tmp_path / "other")
    DeltaTable.create(other, SCHEMA, configuration={"delta.enableChangeDataFeed": "true"})
    append(other, [7, 8])
    b = paid_other(DeltaSource(other)).write(DeltaSink(sink))
    append(src, [3])
    hold(monkeypatch, a, "contract", lambda: b.refresh(engine=engine))
    with pytest.raises(ConcurrentWriteError):
        a.refresh(engine=engine)
    assert ids(sink) == [7, 8]

"""A `DeltaSink`'s table maintenance (checkpoints, log retention, compaction,
vacuum), and a restarted job resuming past maintenance commits, its own or
another writer's, on local tables."""

from datetime import timedelta

import pytest
from deltalake import DeltaTable, write_deltalake

import sverify as sv
from _pipelines import doubled, make_orders, orders_table, paid, recomputed, rows
from sverify.io import DeltaSink, DeltaSource
from sverify.io.delta import METADATA_KEY


@sv.transform()
def ids(t):
    return t.select(t.id)


def job(tmp_path, src=None, **options):
    """`doubled(paid(orders))` stored in `big`; a new job each call."""
    if src is None:
        src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    return src, doubled(paid(src)).write(DeltaSink(str(tmp_path / "big"), **options))


def ops(uri):
    return [c.get("operation") for c in reversed(DeltaTable(uri).history())]


def grow(src, n):
    """Append `n` orders, one commit each, with ids from 10 up."""
    for _ in range(n):
        new = 10 + DeltaTable(src.uri).to_pyarrow_table().num_rows - 2
        write_deltalake(src.uri, orders_table([(new, "cy", 1)]), mode="append")


def vacuum(uri):
    DeltaTable(uri).vacuum(retention_hours=0, dry_run=False, enforce_retention_duration=False)


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
@pytest.mark.parametrize("other", ["optimize", "vacuum", "properties"])
def test_a_restart_resumes_past_another_writers_maintenance(tmp_path, engine, other):
    src, stored = job(tmp_path)
    stored.refresh(engine=engine)
    grow(src, 2)
    stored.refresh(engine=engine)
    uri = str(tmp_path / "big")
    dt = DeltaTable(uri)
    if other == "optimize":
        dt.optimize.compact()
    elif other == "vacuum":
        dt.optimize.compact()
        vacuum(uri)
    else:
        for i in range(10):  # more commits than the first look back reads
            DeltaTable(uri).alter.set_table_properties({"delta.checkpointInterval": str(20 + i)})
    state = DeltaSource(uri).stored()
    assert state is not None and state.sources == {"orders": 3}
    grow(src, 1)
    _, again = job(tmp_path, src)
    entry = again.refresh(engine=engine)["big"]
    assert entry.started == f"resumed from {state.where}"
    assert entry.write is not None and entry.write.mode == "merge"
    assert rows(again) == recomputed(doubled(paid(src)), src)


def test_another_writers_rows_after_the_sink_are_not_resumed_from(tmp_path):
    src, stored = job(tmp_path)
    stored.refresh()
    uri = str(tmp_path / "big")
    DeltaTable(uri).optimize.compact()
    DeltaTable(uri).delete("customer = 'ada'")
    assert DeltaSource(uri).stored() is None
    entry = job(tmp_path, src)[1].refresh()["big"]
    assert entry.started == "computed"


def sink_rows(uri):
    return sorted(DeltaTable(uri).to_pyarrow_table().to_pylist(), key=lambda r: r["id"])


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
@pytest.mark.parametrize("restart", [False, True])
def test_rows_another_writer_changed_are_replaced(tmp_path, engine, restart):
    """#966 (the TLA+ model's `today-foreign` traces): another application
    deletes a row of the sink. The next refresh, of this process or a new
    one, must neither skip (the epoch is committed) nor write a change on
    those rows: it writes the node's rows again."""
    src, stored = job(tmp_path)
    stored.refresh(engine=engine)
    uri = str(tmp_path / "big")
    want = sink_rows(uri)
    DeltaTable(uri).delete("customer = 'ada'")
    node = job(tmp_path, src)[1] if restart else stored
    w = node.refresh(engine=engine)["big"].write
    assert w is not None and w.mode == "overwrite"
    assert sink_rows(uri) == want
    grow(src, 1)
    node.refresh(engine=engine)
    assert sorted(tuple(r.values()) for r in sink_rows(uri)) == recomputed(doubled(paid(src)), src)
    assert node.refresh(engine=engine)["big"].write.mode == "skipped"


def test_table_properties_on_create_and_on_an_existing_table(tmp_path):
    src, stored = job(tmp_path, checkpoint_interval=5, log_retention=timedelta(days=2))
    stored.refresh()
    uri = str(tmp_path / "big")
    config = DeltaTable(uri).metadata().configuration
    assert config["delta.checkpointInterval"] == "5"
    assert config["delta.logRetentionDuration"] == "interval 172800 seconds"
    grow(src, 1)
    _, again = job(tmp_path, src, checkpoint_interval=3)
    w = again.refresh()["big"].write
    assert w is not None and w.mode == "merge"
    assert DeltaTable(uri).metadata().configuration["delta.checkpointInterval"] == "3"
    assert ops(uri)[-2] == "SET TBLPROPERTIES"


def test_checkpoints_follow_the_interval(tmp_path):
    src, stored = job(tmp_path, checkpoint_interval=2)
    stored.refresh()
    for _ in range(4):
        grow(src, 1)
        stored.refresh()
    log = tmp_path / "big" / "_delta_log"
    assert sorted(p.name for p in log.glob("*.checkpoint.parquet"))


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_compact_every_compacts_with_the_contract(tmp_path, engine):
    src, stored = job(tmp_path, compact_every=2, vacuum_retention=timedelta(0))
    uri = str(tmp_path / "big")
    stored.refresh(engine=engine)
    grow(src, 1)
    stored.refresh(engine=engine)
    history = DeltaTable(uri).history()
    assert [c["operation"] for c in history[:3]] == ["VACUUM END", "VACUUM START", "OPTIMIZE"]
    # The maintenance commits carry the contract, and add no transaction.
    contract = DeltaSource(uri).contract()
    assert contract is not None and contract.sources == {"orders": 2}
    assert all(METADATA_KEY in c for c in history[:3])
    assert DeltaTable(uri).transaction_version("sverify:big") == 2
    assert len(list((tmp_path / "big").glob("*.parquet"))) == 1
    # Writes go on, and a restarted job resumes from the compacted table.
    grow(src, 1)
    stored.refresh(engine=engine)
    _, again = job(tmp_path, src)
    entry = again.refresh(engine=engine)["big"]
    assert entry.started is not None and entry.started.startswith("resumed from")
    assert entry.write is not None and entry.write.mode == "skipped"
    assert rows(again) == recomputed(doubled(paid(src)), src)


def test_a_node_reading_the_sink_reads_past_a_compaction(tmp_path):
    src, stored = job(tmp_path, compact_every=1)
    reader = ids(stored)
    reader.refresh()
    grow(src, 1)
    entry = reader.refresh()["ids"]
    assert entry.report is not None and entry.report.sources[0].mode == "change_feed"
    assert "OPTIMIZE" in ops(str(tmp_path / "big"))
    assert rows(reader) == [(1,), (2,), (10,)]


def test_maintain_without_the_contract_after_another_writer(tmp_path):
    src, stored = job(tmp_path)
    stored.refresh()
    uri = str(tmp_path / "big")
    DeltaTable(uri).delete("customer = 'ada'")
    sink = DeltaSink(uri)
    out = sink.maintain()
    assert "optimize" in out and "vacuumed" not in out
    assert METADATA_KEY not in DeltaTable(uri).history(1)[0]
    assert DeltaSource(uri).stored() is None


def test_maintain_on_no_table_does_nothing(tmp_path):
    assert DeltaSink(str(tmp_path / "none")).maintain() == {}


def test_options_are_checked(tmp_path):
    with pytest.raises(ValueError, match="compact_every"):
        DeltaSink(str(tmp_path / "t"), compact_every=0)
    with pytest.raises(ValueError, match="checkpoint_interval"):
        DeltaSink(str(tmp_path / "t"), checkpoint_interval=0)

"""An engine that raises commits nothing (#1130, obligation 4).

`docs/trusted-base.md` lists it beside `Engine.Runs`: the theorem says
nothing about a run that raises, so the sink must be left as it was. Each
sink kind is checked twice: an engine error a refresh raises (the engine's
runner fails mid-run), and a run-time check that fires (the node is held,
ruling 258). Spark's ANSI raise reaches the same path through its runner.
"""

from __future__ import annotations

import dataclasses
import warnings
from collections.abc import Callable
from typing import Any

import pyarrow as pa
import pytest
from deltalake import DeltaTable
from ibis import _

import sverify as sv
from sverify import profiles
from sverify.incremental import Changes
from sverify.io import DeltaSink, StaticSource, sink_from


def _table(rows: list[tuple[int, float]]) -> pa.Table:
    return pa.table({"id": [r[0] for r in rows], "value": [r[1] for r in rows]})


def _delta(tmp_path) -> tuple[Any, Callable[[], Any]]:
    path = str(tmp_path / "out")

    def state():
        t = DeltaTable(path)
        return t.version(), sorted(t.to_pyarrow_table().to_pylist(), key=lambda r: r["id"])

    return DeltaSink(path), state


def _iceberg(tmp_path) -> tuple[Any, Callable[[], Any]]:
    pytest.importorskip("pyiceberg")
    from pyiceberg.catalog.sql import SqlCatalog

    from sverify.io import IcebergSink

    warnings.filterwarnings("ignore", module="pyiceberg")
    cat = SqlCatalog("test", uri=f"sqlite:///{tmp_path}/catalog.db", warehouse=f"file://{tmp_path}")
    cat.create_namespace("db")

    def state():
        t = cat.load_table("db.out")
        snap = t.current_snapshot()
        rows = t.scan().to_arrow().to_pylist()
        return snap.snapshot_id if snap else None, sorted(rows, key=lambda r: r["id"])

    return IcebergSink(cat, "db.out"), state


def _custom(tmp_path) -> tuple[Any, Callable[[], Any]]:
    written: list[pa.Table] = []

    def state():
        return len(written), sorted(written[-1].to_pylist(), key=lambda r: r["id"])

    return sink_from(written.append, name="out"), state


SINKS = {"delta": _delta, "iceberg": _iceberg, "custom": _custom}


def _node(src: StaticSource, sink: Any) -> Any:
    @sv.transform(requires={"t": [_.value >= 0]}, ensures=[_.scaled.isnull() | (_.scaled >= 0)])
    def scaled(t):
        return t.select("id", scaled=t.value * 1e300)

    return src.pipe(scaled).write(sink)


@pytest.mark.parametrize("kind", SINKS)
def test_an_engine_error_commits_nothing(tmp_path, monkeypatch, kind):
    sink, state = SINKS[kind](tmp_path)
    src = StaticSource(_table([(1, 1.0)]), name="t")
    node = _node(src, sink)
    assert node.refresh().outcome == "ok"
    before = state()

    duckdb = profiles.find("duckdb")
    assert duckdb is not None

    def fails(*args, **kwargs):
        raise RuntimeError("the engine died mid-run")

    monkeypatch.setitem(profiles.plugins(), "duckdb", dataclasses.replace(duckdb, runner=fails))
    src.apply(Changes(inserts=_table([(2, 2.0)])))
    with pytest.raises(RuntimeError, match="died mid-run"):
        node.refresh()
    assert state() == before


@pytest.mark.parametrize("kind", SINKS)
def test_a_fired_check_commits_nothing(tmp_path, kind):
    sink, state = SINKS[kind](tmp_path)
    src = StaticSource(_table([(1, 1.0)]), name="t")
    node = _node(src, sink)
    assert node.refresh().outcome == "ok"
    before = state()
    src.apply(Changes(inserts=_table([(2, 1e200)])))  # overflows to infinity
    assert node.refresh().outcome == "held"
    assert state() == before

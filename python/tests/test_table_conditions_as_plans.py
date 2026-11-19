"""Table conditions are counted by the engine that runs their plan (#1764, ruling
118): the reference's meaning on every engine, one plan per table, no Ibis
execution on the connection's backend, and a writer that refuses refuses the
check."""

from __future__ import annotations

from datetime import timedelta

import pyarrow as pa
import pytest

import sverify as sv
from sverify import report as report_module
from sverify.conditions import ArrivesWithin, MaxRows, References, RowsPer, Unique
from sverify.errors import UnsupportedError
from sverify.report import violation_counts

#: NULL keys (`k`, `j`), a NULL foreign key (`fk`), a NULL time.
ROWS = {
    "k": [None, None, 1, 1, 1, 2],
    "j": [1, 1, 1, None, None, 2],
    "ts": pa.array([None, 1, 2, 3, 4, 5], pa.timestamp("us")),
    "fk": [None, 5, 6, 9, None, 5],
}
CONDS = [
    Unique(("k",)),
    Unique(("k", "j")),
    Unique(("j",)),
    References("fk", "p", "id"),
    MaxRows(4),
    MaxRows(10),
    RowsPer(("k",), 2),
    RowsPer((), 2),
    RowsPer(("j",), 1),
    ArrivesWithin("ts", timedelta(hours=1)),
]
#: The counts DuckDB's Ibis path gave before the plans (the specification): NULL
#: keys are one key in `unique` and `rows_per`; a NULL foreign key is no violation.
WANT = [3, 2, 3, 1, 2, 0, 1, 4, 3, 1]


@pytest.fixture(params=["duckdb", "polars", "spark"])
def engine(request: pytest.FixtureRequest) -> str:
    if request.param != "duckdb":
        pytest.importorskip("pyspark" if request.param == "spark" else request.param)
    return request.param


@pytest.fixture
def table(engine: str):
    con = sv.connect("polars" if engine == "polars" else None)
    con.put("t", pa.table(ROWS))
    con.put("p", pa.table({"id": [5, 6]}))
    con.put("e", pa.table({"k": pa.array([], pa.int64())}))
    return con


def test_counts_with_null_keys_are_the_same_on_every_engine(table, engine):
    got = [n for _, n, _ in violation_counts(table.table("t"), CONDS, engine)]
    assert got == WANT


def test_an_empty_table_breaks_nothing(table, engine):
    conds = [Unique(("k",)), MaxRows(0), RowsPer(("k",), 1), RowsPer((), 0)]
    assert [n for _, n, _ in violation_counts(table.table("e"), conds, engine)] == [0] * 4


def test_the_conditions_of_a_table_run_as_one_plan(table, monkeypatch):
    runs: list[str] = []
    real = report_module.run_plan

    def spy(con, plan, engine, **kw):
        runs.append(engine)
        return real(con, plan, engine, **kw)

    monkeypatch.setattr(report_module, "run_plan", spy)
    got = [n for _, n, _ in violation_counts(table.table("t"), CONDS, table.engine)]
    assert got == WANT and len(runs) == 1


def test_no_ibis_expression_runs_on_the_connections_backend(table, monkeypatch):
    import ibis.expr.types as ir

    def refuse(*args, **kwargs):
        raise AssertionError("an Ibis expression was executed on the connection's backend")

    monkeypatch.setattr(ir.Expr, "to_pyarrow", refuse)
    monkeypatch.setattr(ir.Expr, "execute", refuse)
    assert violation_counts(table.table("t"), CONDS, table.engine)[0][1] == 3


def test_a_condition_the_writer_refuses_refuses_the_check(table, monkeypatch):
    def refuse(*args, **kwargs):
        raise UnsupportedError("the writer does not take this")

    monkeypatch.setattr(report_module, "run_plan", refuse)
    with pytest.raises(UnsupportedError):
        violation_counts(table.table("t"), CONDS, table.engine)


def test_a_table_of_the_callers_own_backend_is_counted_there(monkeypatch):
    """Its rows stay in that backend (no copy through Python into a connection),
    and the counts are the same."""
    pytest.importorskip("duckdb")
    import ibis

    backend = ibis.duckdb.connect()
    backend.create_table("t", pa.table(ROWS))
    backend.create_table("p", pa.table({"id": [5, 6]}))

    def refuse(*args, **kwargs):
        raise AssertionError("a table of the caller's backend was copied into a connection")

    monkeypatch.setattr(sv, "connect", refuse)
    got = [n for _, n, _ in violation_counts(backend.table("t"), CONDS, None)]
    assert got == WANT

"""`requires` are checked on the run's own engine (S3, #1484), as the plan the
checker wrote for each table, and DuckDB's proved translation is not run
twice for its assumptions (S4)."""

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from _engines import PROFILED
from sverify import report as report_module
from sverify.engine import connect, put_table, written_plan
from sverify.errors import PreconditionError, UnsupportedError

T = ibis.table({"x": "int64"}, name="t")
F = ibis.table({"x": "float64"}, name="f")


def _con(rows: list[int]):
    con = connect()
    put_table(con, "t", pa.table({"x": pa.array(rows, pa.int64())}))
    return con


@pytest.mark.parametrize("engine", PROFILED)
def test_a_violated_requires_refuses_the_run_on_each_engine(engine):
    report = sv.verify(T.select(y=_.x + 1), requires={"t": [_.x >= 0, _.x < 100]})
    assert report.verdict == sv.Verdict.PROVED
    assert report.run(_con([0, 5]), engine).num_rows == 2
    with pytest.raises(
        PreconditionError, match=r"1 row\(s\) of t violate .*refused before the run"
    ):
        report.run(_con([0, -1]), engine)


@pytest.mark.parametrize("engine", PROFILED)
def test_a_condition_that_raises_is_a_violation(engine):
    """`10 // x > 1` raises on `x = 0`: the batch is refused, whichever engine."""
    report = sv.verify(
        "SELECT x FROM t", tables={"t": T}, requires={"t": ["x <> 0 AND 10 // x > 1"]}
    )
    with pytest.raises(PreconditionError, match="refused before the run"):
        report.run(_con([0, 2]), engine)


def test_a_condition_the_engine_writer_refuses_refuses_the_run():
    """No fallback to Ibis: `%` of doubles is refused on Polars (#1270)."""
    report = sv.verify(F.select(y=_.x + 1.0), requires={"f": [(_.x % 2.0) >= 0.0]})
    con = connect()
    put_table(con, "f", pa.table({"x": [1.0, 3.0]}))
    with pytest.raises(UnsupportedError):
        report.run(con, "polars")


def test_a_duckdb_run_with_assumptions_runs_the_plan_once(monkeypatch):
    """The proved translation checks the assumed `SUM`s as it runs; the plan is
    not run once more beforehand."""
    report = sv.verify(
        "SELECT SUM(x) AS s FROM t",
        tables={"t": T},
        requires={"t": [_.x.between(-(10**15), 10**15)]},
    )
    assert report.assumed
    main = written_plan(report.internal_plan)
    runs: list[str] = []
    real = report_module.run_plan

    def spy(con, plan, engine, **kw):
        if plan == main:
            runs.append(engine)
        return real(con, plan, engine, **kw)

    monkeypatch.setattr(report_module, "run_plan", spy)
    report.run(_con([1, 2, 3]), "duckdb")
    assert runs == ["duckdb"]

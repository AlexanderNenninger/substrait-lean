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
    assert report.assumed and report.internal_plan
    main = written_plan(report.internal_plan)
    runs: list[str] = []
    real = report_module._run_plan

    def spy(con, plan, engine, **kw):
        if plan == main:
            runs.append(engine)
        return real(con, plan, engine, **kw)

    monkeypatch.setattr(report_module, "_run_plan", spy)
    report.run(_con([1, 2, 3]), "duckdb")
    assert runs == ["duckdb"]


@pytest.mark.parametrize("engine", ["polars", "spark"])
def test_a_polars_or_spark_run_with_assumptions_does_not_run_on_duckdb(engine, monkeypatch):
    """Their translations check the assumed `SUM`s as they run (#1484): the plan
    runs on the target engine only, and a batch that breaks one is refused."""
    pytest.importorskip("pyspark" if engine == "spark" else "polars")
    report = sv.verify(
        "SELECT SUM(x) AS s FROM t",
        tables={"t": T},
        requires={"t": [_.x.between(-(10**18), 10**18)]},
    )
    assert report.assumed and report.internal_plan
    runs: list[str] = []
    real = report_module._run_plan

    def spy(con, plan, eng, **kw):
        runs.append(eng if isinstance(eng, str) else "session")
        return real(con, plan, eng, **kw)

    monkeypatch.setattr(report_module, "_run_plan", spy)
    out = report.run(_con([1, 2, 3]), engine)
    assert out.to_pylist() == [{"s": 6}]
    assert "duckdb" not in runs
    with pytest.raises(PreconditionError, match="assumed precondition"):
        report.run(
            _con([10**18, 10**18, 10**18, 10**18, 10**18, 10**18, 10**18, 10**18, 10**18, 10**18]),
            engine,
        )


def test_polars_checks_the_assumed_sum_on_the_guard_free_route_too(monkeypatch):
    """A guard-free report on Polars runs without its other checks, and the
    assumed `SUM` keeps its own (`NO_GUARDS`): a batch that breaks it is
    refused on that route (#1484)."""
    pytest.importorskip("polars")
    report = sv.verify(
        "SELECT SUM(x) AS s FROM t",
        tables={"t": T},
        requires={"t": [_.x.between(-(10**18), 10**18)]},
    )
    assert report._guard_free and report.assumed
    routes: list[str] = []
    real = report_module.run_guard_free

    def spy(*args, **kw):
        routes.append("guard_free")
        return real(*args, **kw)

    monkeypatch.setattr(report_module, "run_guard_free", spy)
    assert report.run(_con([1, 2, 3]), "polars").to_pylist() == [{"s": 6}]
    assert routes == ["guard_free"]
    with pytest.raises(PreconditionError, match="assumed precondition"):
        report.run(_con([10**18] * 10), "polars")


def test_a_check_with_no_engine_named_runs_the_proved_plan(monkeypatch):
    """F219 (#2342): with `check_engine=None`, a transform's `requires` on a
    bound input run as the checker's plan on the connection's engine, all of
    one table's conditions in one plan, and a violation still refuses it."""
    runs: list[str] = []
    real = report_module._run_conditions

    def spy(con, table, conds, engine):
        runs.append(engine)
        return real(con, table, conds, engine)

    monkeypatch.setattr(report_module, "_run_conditions", spy)

    @sv.transform(requires={"t": [_.x >= 0, _.x < 100]})
    def plus_one(t):
        return t.select(y=t.x + 1)

    assert plus_one(_con([0, 5]).table("t")).to_pyarrow().num_rows == 2
    assert runs == ["duckdb"]
    with pytest.raises(PreconditionError, match=r"1 row\(s\) of t violate"):
        plus_one(_con([0, -1]).table("t"))


def test_a_table_of_the_callers_own_backend_is_checked_by_ibis(monkeypatch):
    """F219 (#2342): a table of a plain Ibis backend has no sverify engine,
    so with `check_engine` unset Ibis counts its conditions there, and a
    violation still refuses the call."""
    runs: list[str] = []
    real = report_module._run_conditions

    def spy(con, table, conds, engine):
        runs.append(engine)
        return real(con, table, conds, engine)

    monkeypatch.setattr(report_module, "_run_conditions", spy)

    @sv.transform(requires={"t": [_.x >= 0, _.x < 100]})
    def plus_one(t):
        return t.select(y=t.x + 1)

    def table(rows: list[int]):
        backend = ibis.duckdb.connect()
        backend.con.register("t", pa.table({"x": pa.array(rows, pa.int64())}))
        return backend.table("t")

    assert plus_one(table([0, 5])).to_pyarrow().num_rows == 2
    with pytest.raises(PreconditionError, match=r"1 row\(s\) of t violate"):
        plus_one(table([0, -1]))
    assert runs == []


@pytest.fixture
def berlin(monkeypatch):
    """The host, and DuckDB's global setting, in Europe/Berlin (#2280's way of
    setting the host zone), restored afterwards."""
    import time

    from sverify import _duckdb

    if not hasattr(time, "tzset"):
        pytest.skip("the host zone is set with time.tzset, which Windows lacks")
    monkeypatch.setenv("TZ", "Europe/Berlin")
    time.tzset()
    cursor = _duckdb.cursor()
    cursor.execute("SET GLOBAL TimeZone = 'Europe/Berlin'").fetchall()
    yield
    cursor.execute("RESET GLOBAL TimeZone").fetchall()
    monkeypatch.undo()
    time.tzset()


def test_a_utc_instant_round_trips_through_a_check_outside_utc(berlin):
    """sverify's DuckDB cursors run at UTC (#2342): a batch's UTC instant comes
    back zoned UTC on a host in another zone, so the checker-written plan of a
    precondition reads it, and the node's rows keep their zone."""
    import datetime as dt

    from sverify.io import Changes, StaticSource

    utc = pa.timestamp("us", tz="UTC")
    t0 = dt.datetime(2026, 11, 3, tzinfo=dt.UTC)

    def rows(minutes: list[int]) -> pa.Table:
        return pa.table(
            {"ts": [t0 + dt.timedelta(minutes=m) for m in minutes], "cpu": [1] * len(minutes)},
            schema=pa.schema([("ts", utc), ("cpu", pa.int64())]),
        )

    @sv.transform(requires={"s": [_.cpu.notnull(), _.cpu >= 0]})
    def busy(s):
        return s.filter(s.cpu > 0)

    src = StaticSource(rows([0]), name="s")
    node = src.pipe(busy)
    node.refresh()
    src.apply(Changes(inserts=rows([5])))
    node.refresh()
    out = node.to_arrow()
    assert out.schema.field("ts").type == utc
    assert sorted(out.column("ts").to_pylist()) == [t0, t0 + dt.timedelta(minutes=5)]

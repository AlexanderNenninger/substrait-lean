"""A checked run writes the expressions the checker marked without their
checks (ruling 223, #1787 item 1a).

On a checked, translated run under the reference, `Report.run` hands the marks
of the plan that runs (`Rel.marks`) to an engine the checker names a
`"marks_theorem"` for (DuckDB: `Rel.duckdb_marks`). Those expressions are
written without their guards and without the check against `±∞`
(`Expr.issues_nil_of_safe`); everything else keeps its checks."""

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from _repo import needs_repo
from sverify.engine import connect, put_table
from sverify.engines.plan import to_sql
from sverify.errors import PreconditionError
from sverify_duckdb import engine as duckdb_engine

T = ibis.table({"k": "int64", "x": "float64", "y": "float64"}, name="t")
BOUNDED = {"t": [ibis._.x.between(-1e6, 1e6), ibis._.y.between(1.0, 1e6)]}
PLAN = T.select(T.k, v=T.x * T.y + T.x / T.y)


@pytest.fixture
def seen(monkeypatch) -> list[dict | None]:
    """The marks each DuckDB run was given."""
    found: list[dict | None] = []
    run = duckdb_engine.run

    def spy(plan, tables, **kw):
        found.append(kw.get("unchecked"))
        return run(plan, tables, **kw)

    monkeypatch.setattr(duckdb_engine, "run", spy)
    return found


def _table(x: list[float], y: list[float]) -> pa.Table:
    return pa.table({"k": list(range(len(x))), "x": x, "y": y})


def _con(x: list[float], y: list[float]):
    con = connect()
    put_table(con, "t", _table(x, y))
    return con


def test_a_checked_run_drops_the_marked_checks(seen):
    """M1, M2: the run hands DuckDB the marks of the plan it runs; the
    written SQL drops the guards and the check against `±∞` of the marked
    expression, and gives the rows the fully checked SQL gives."""
    report = sv.verify(PLAN, requires=BOUNDED, ensures=[sv.equivalent(floats="exact")])
    assert (report._engines or {})["duckdb"]["marks_theorem"] == "Rel.duckdb_marks_written"
    con = _con([1.0, -2.5, 1e6], [1.0, 2.0, 1e6])
    out = report.run(con, "duckdb")
    assert seen[-1] is not None
    plan = report._plan_to_run("translated", checked=True, engine="duckdb")
    marked = to_sql(plan, "duckdb", unchecked=seen[-1])
    assert "overflow to infinity" not in marked
    assert "overflow to infinity" in to_sql(plan, "duckdb")
    full = duckdb_engine.run(plan, {"t": _table([1.0, -2.5, 1e6], [1.0, 2.0, 1e6])})
    assert out.to_pylist() == full.to_pylist()


def test_an_unchecked_run_keeps_every_check(seen):
    """M1: `check_requires=False` writes every check."""
    report = sv.verify(PLAN, requires=BOUNDED, ensures=[sv.equivalent(floats="exact")])
    report.run(_con([1.0], [1.0]), "duckdb", check_requires=False)
    assert seen[-1] is None


def test_data_that_breaks_a_precondition_is_refused_before_the_run(seen):
    """M8: the unguarded statement never runs on data outside the contract."""
    report = sv.verify(PLAN, requires=BOUNDED, ensures=[sv.equivalent(floats="exact")])
    with pytest.raises(PreconditionError):
        report.run(_con([1e300], [1e300]), "duckdb")
    # The checks of the preconditions run; no statement with marks does.
    assert all(m is None for m in seen)


def test_an_assumed_issue_is_never_marked(seen):
    """M5: with finite but wide bounds the product may overflow, an assumed issue; its
    expression has no mark, so its check against `±∞` stays in the SQL."""
    finite = {"t": [ibis._.x.between(-1e300, 1e300), ibis._.y.between(-1e300, 1e300)]}
    report = sv.verify(
        T.select(T.k, v=T.x * T.y), requires=finite, ensures=[sv.equivalent(floats="exact")]
    )
    assert [i.kind for i in report.assumed] == ["overflow to infinity"]
    report.run(_con([1.0], [2.0]), "duckdb")
    plan = report._plan_to_run("translated", checked=True, engine="duckdb")
    assert "overflow to infinity" in to_sql(plan, "duckdb", unchecked=seen[-1])


#: The catalogue plans whose marks are of another shape than the plan the
#: writer reads, so they keep every check (ruling 226, N4): each has a decimal
#: `AVG`, which the checker reads as a sum and a count and the writer folds
#: back. A new fold that drops other plans' marks fails here.
DROPPED = {"tpcds-q07", "tpch-q01", "tpch-q17", "tpch-q22"}


@needs_repo
@pytest.mark.slow
def test_catalogue_runs_give_the_same_rows_with_marks():
    """M8: on every catalogue query with marks, DuckDB gives the same rows
    with and without them, on synthetic data that meets the contract; and
    only `DROPPED`'s plans lose their marks to their shape (N4)."""
    from sverify_dev import catalogue

    schemas = catalogue.load_schemas()
    ran = 0
    dropped = set()
    for q in catalogue.load_queries():
        if q.not_expressible is not None or q.requires is None:
            continue
        try:
            requires, ensures = catalogue.contract(q, schemas, "native")
            report = sv.verify(catalogue.build(q, schemas, "native"), requires=requires,
                               ensures=ensures)  # fmt: skip
        except Exception:  # noqa: BLE001 - a query the checker refuses
            continue
        if report.verdict == sv.Verdict.UNPROVED:
            continue
        plan = report._plan_to_run("translated", checked=True, engine="duckdb")
        given = report._run_unchecked if report._run_plan is not None else report._unchecked
        marks = report._marks_of(plan)
        if given is not None and marks is None:
            dropped.add(q.id)
        if marks is None:
            continue
        data = catalogue.synthetic(schemas, q.dataset, "native")
        con = connect()
        for t, table in data.items():
            put_table(con, t, table)
        if catalogue.requires_hold(con, requires) is not None:
            continue
        try:
            full = duckdb_engine.run(plan, data)
        except Exception:  # noqa: BLE001 - a run that raises on the data either way
            continue
        bare = duckdb_engine.run(plan, data, unchecked=marks)
        assert catalogue._canonical(catalogue._rows(bare)) == catalogue._canonical(
            catalogue._rows(full)
        ), q.id
        ran += 1
    assert ran > 10
    assert dropped == DROPPED


@needs_repo
def test_the_checkers_marks_fit_the_plans_it_writes():
    """B6 (a): for the contract goldens, the marks the checker gives fit the
    plan it writes (`written_plan`), so a run never falls back on them; the
    catalogue's plans are the slow test above, decimal `AVG` excepted."""
    import json

    from _repo import ROOT
    from sverify._checker import run_checker
    from sverify.engine import written_plan
    from sverify.sql.core._base import parse_plan, unchecked_slots

    fit = 0
    for path in sorted((ROOT / "tests" / "contracts").glob("*.json")):
        request = json.loads(path.read_text())
        code, out, _ = run_checker(("--contract",), path.read_text())
        marks = json.loads(out).get("unchecked") if code == 0 else None
        if marks is None:
            continue
        plan = written_plan(json.dumps(request["transform"]))
        unchecked_slots(parse_plan(json.loads(plan)).root, marks)
        fit += 1
    assert fit > 0


def test_the_marks_stay_on_their_slots_across_a_bound_layer():
    """B6 (b): the checker writes `x * y + a / b` with the product and the
    quotient bound as columns of their own; the product (`x`, `y` bounded) is
    marked and the quotient (`b` free) is not. The marked SQL drops only the
    product's checks, and on data where the quotient raises it raises as the
    SQL without marks does."""
    import duckdb

    from sverify.engine import written_plan

    u = ibis.table({"x": "float64", "y": "float64", "a": "float64", "b": "float64"}, name="u")
    q = u.select(v=u.x * u.y + u.a / u.b)
    report = sv.verify(
        q, requires={"u": [ibis._.x.between(0, 10), ibis._.y.between(0, 10)]}, on_inferred="off"
    )
    marks = report._unchecked
    assert marks is not None
    bound = marks["inputs"][0]["inputs"][0]
    assert bound["node"] == "Project" and bound["slots"] == [0]
    assert report.internal_plan is not None
    plan = written_plan(report.internal_plan)
    marked, full = to_sql(plan, "duckdb", unchecked=marks), to_sql(plan, "duckdb")
    assert marked.count("sverify: ") < full.count("sverify: ")
    assert "division by zero" in marked
    con = duckdb.connect()
    con.register("u", pa.table({"x": [1.0], "y": [2.0], "a": [1.0], "b": [0.0]}))
    for sql in (full, marked):
        with pytest.raises(duckdb.Error, match="division by zero"):
            con.execute(sql).fetchall()

"""A checked run leaves out the ordinal that keeps Lean's row order where the
checker proved the observation cannot see it (#1787 item 2, ruling 223 O1–O4):
under a multiset lens on an exact report (`check_deterministic_sound`), and
under a sequence lens on a sequence-determined one
(`check_sequence_determined_sound`). The result equals the run with the
ordinal, as the lens compares, on each engine whose runner numbers rows."""

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify import report as report_module
from sverify.engine import written_plan
from sverify.sql import to_sql
from sverify_duckdb.dialect import DUCKDB

pytestmark = pytest.mark.backend("duckdb")

T = ibis.table({"id": "int64", "g": "int64", "v": "int64"}, name="t")
REQUIRES = {"t": [_.id.notnull(), sv.unique("id")]}
SEQUENCE = sv.equivalent(rows="sequence")

FREE = {
    "top-n by a key": (T.order_by("id").limit(3), None),
    "top-n by a key, in sequence": (T.order_by("id").limit(3), SEQUENCE),
    "window ordered by a key": (
        T.mutate(n=ibis.row_number().over(group_by="g", order_by="id")),
        None,
    ),
    "aggregate": (T.group_by("g").agg(s=T.v.sum()), None),
}
KEPT = {
    "top-n with ties": (T.order_by("g").limit(3), None),
    "window with ties": (T.mutate(n=ibis.row_number().over(group_by="g", order_by="v")), None),
}
ROWS = pa.table(
    {
        "id": [7, 3, 9, 1, 5, 2, 8],
        "g": [1, 2, 1, 2, 1, 3, 3],
        "v": [10, 20, 30, 40, 50, 60, 70],
    }
)


def _con():
    con = sv.connect()
    con.put("t", ROWS)
    return con


def _report(case: tuple):
    expr, lens = case
    return sv.verify(expr, requires=REQUIRES, ensures=[lens] if lens else [])


def _spy(monkeypatch) -> list:
    """The `rows` each run hands its runner, on either route."""
    seen: list = []
    for name in ("_run_plan", "run_guard_free"):
        real = getattr(report_module, name)

        def spy(*args, _real=real, **kw):
            seen.append(kw.get("rows"))
            return _real(*args, **kw)

        monkeypatch.setattr(report_module, name, spy)
    return seen


def _as_lens(t: pa.Table, lens) -> list:
    rows = [tuple(r.values()) for r in t.to_pylist()]
    return rows if lens is SEQUENCE else sorted(rows)


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
@pytest.mark.parametrize("case", FREE, ids=list(FREE))
def test_a_checked_run_drops_the_ordinal_and_gives_the_same_rows(engine, case, monkeypatch):
    """O4: with and without the ordinal, equal as the lens compares."""
    pytest.importorskip(engine)
    report = _report(FREE[case])
    assert report._ordinal_free
    seen = _spy(monkeypatch)
    with_ordinal = report.run(_con(), engine, check_requires=False)
    without = report.run(_con(), engine)
    assert seen == [None, "multiset"]
    lens = FREE[case][1]
    assert _as_lens(without, lens) == _as_lens(with_ordinal, lens)


@pytest.mark.parametrize("case", KEPT, ids=list(KEPT))
def test_open_rows_keep_the_ordinal(case, monkeypatch):
    """O1: ties that a LIMIT or a window's numbering picks among keep it."""
    report = _report(KEPT[case])
    assert not report._ordinal_free
    seen = _spy(monkeypatch)
    report.run(_con(), "duckdb")
    assert seen == [None]


def test_duckdb_reads_its_inputs_without_numbering_them():
    """Without the ordinal, DuckDB's SQL reads no `rowid`, so an input needs
    no copy (O4)."""
    report = _report(FREE["window ordered by a key"])
    assert report.internal_plan is not None
    plan = written_plan(report.internal_plan)
    assert DUCKDB.row_ordinal() in to_sql(plan, DUCKDB)
    assert DUCKDB.row_ordinal() not in to_sql(plan, DUCKDB, rows="multiset", deterministic=True)

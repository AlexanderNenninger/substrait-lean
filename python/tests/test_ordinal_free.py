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


#: Each case and the place of its sort key, `g`, in the output.
SORTED = {
    "sort": (T.order_by("g"), 1),
    "sort, selected": (T.order_by(ibis.desc("g")).select("g", "v"), 0),
    "top-n": (T.order_by("g").limit(4, offset=1), 1),
}


@pytest.mark.parametrize("case", SORTED, ids=list(SORTED))
def test_a_sorted_root_sorts_by_its_keys_under_a_multiset(case):
    """Under `rows="multiset"` a root sort, or a top-N, sorts the result by its
    own keys and numbers no rows, in every dialect (#2186, ruling 217 S3);
    ties stay open, so on DuckDB the rows are the sequence run's up to ties."""
    from sverify.sql.snowflake import SNOWFLAKE
    from sverify_spark.dialect import SPARK

    expr, key = SORTED[case]
    report = sv.verify(expr)
    assert report.internal_plan is not None
    plan = written_plan(report.internal_plan)
    for d in (DUCKDB, SPARK, SNOWFLAKE):
        sql = to_sql(plan, d, rows="multiset")
        assert "ROW_NUMBER" not in sql.upper(), (d.name, sql)
    import duckdb

    con = duckdb.connect()
    con.register("rows", ROWS)
    con.execute("CREATE TABLE t AS SELECT * FROM rows")
    multiset = con.execute(to_sql(plan, DUCKDB, rows="multiset")).fetchall()
    sequence = con.execute(to_sql(plan, DUCKDB, rows="sequence")).fetchall()
    if case != "top-n":  # a top-N keeps any of its ties
        assert sorted(multiset) == sorted(sequence)
    assert [r[key] for r in multiset] == [r[key] for r in sequence]  # ties may differ

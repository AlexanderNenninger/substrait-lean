"""A run-time check that fires in a refresh holds the node (ruling 258, #2331).

`fired_check` is the one classifier: the writer's `sverify: ` raise text for
DuckDB, Spark and Snowflake, `RuntimeIssue` for Polars. Anything else is not a
fired check, and a refresh raises it as before.
"""

import duckdb
import pyarrow as pa
import pytest
from deltalake import DeltaTable
from ibis import _

import sverify as sv
from sverify._fired import fired_check
from sverify.errors import UnsupportedError
from sverify.incremental import Changes
from sverify.io import DeltaSink, StaticSource
from sverify.nodes import Group
from sverify.sql import dialect_of

#: One table whose product overflows to infinity.
BIG = pa.table({"id": [1, 2], "value": [1.0, 1e300]})


def _node():
    @sv.transform(requires={"t": [_.value >= 0]}, ensures=[_.scaled.isnull() | (_.scaled >= 0)])
    def scaled(t):
        return t.select("id", scaled=t.value * 1e300)

    return StaticSource(BIG, name="t").pipe(scaled)


def test_a_fired_check_holds_the_node_on_duckdb():
    r = _node().refresh()
    entry = r.nodes[0]
    assert r.outcome == "held" and entry.held is not None
    assert entry.held.startswith("a run-time check fired: overflow to infinity;")
    assert "nothing was committed" in entry.held
    alert = r.alert()
    assert alert is not None and "requires=" in alert and "1e300" not in alert


def test_a_fired_check_names_no_row_value():
    held = _node().refresh().nodes[0].held
    assert held is not None and "inf" not in held.split(";")[0].replace("infinity", "")


def test_a_crash_is_not_a_fired_check():
    assert fired_check(RuntimeError("disk full")) is None
    assert fired_check(duckdb.IOException("cannot open file")) is None
    # A sverify error whose text mentions the writer's prefix is still an error.
    assert fired_check(UnsupportedError("sverify: x: y")) is None


@pytest.mark.parametrize("engine", ["duckdb", "spark", "snowflake"])
def test_each_dialect_writes_the_guard_text_the_classifier_reads(engine):
    sql = dialect_of(engine).raise_("overflow to infinity", "x", "float", "infinite")
    assert "sverify: overflow to infinity: " in sql


@pytest.mark.parametrize(
    "text",
    [
        "Invalid Input Error: sverify: overflow to infinity: inf",  # DuckDB
        "[USER_RAISED_EXCEPTION] sverify: overflow to infinity: inf SQLSTATE: P0001",  # Spark
        "Numeric value 'sverify: overflow to infinity: inf' is not recognized",  # Snowflake
    ],
)
def test_an_engines_raise_of_the_guard_is_recognised(text):
    assert fired_check(RuntimeError(text)) == "overflow to infinity"


def test_a_guard_quoted_in_another_errors_sql_is_not_a_fired_check():
    """DuckDB quotes the SQL around an error, and that SQL holds the guard's
    literal: a writer bug is a crash, not a hold."""
    con = duckdb.connect()
    sql = (
        "select CASE WHEN x > 1 THEN error(concat('sverify: list_sum out of range: ', "
        "'abc'::INT::VARCHAR)) ELSE x END from (select 5 as x)"
    )
    with pytest.raises(duckdb.ConversionException) as quoted:
        con.execute(sql)
    assert "sverify: list_sum out of range" in str(quoted.value)
    assert fired_check(quoted.value) is None
    with pytest.raises(duckdb.InvalidInputException) as raised:
        con.execute("select error(concat('sverify: overflow to infinity: ', 'inf'))")
    assert fired_check(raised.value) == "overflow to infinity"


def test_polars_raises_a_runtime_issue_that_is_a_fired_check():
    pytest.importorskip("polars")
    from sverify_polars.engine import Overflow

    assert fired_check(Overflow("integer overflow")) == "overflow"
    assert fired_check(ArithmeticError("overflow")) is None


# -- the held state (ruling 260) ------------------------------------------------


def _sink_node(src, path, scale=1e300):
    @sv.transform(requires={"t": [_.value >= 0]}, ensures=[_.scaled.isnull() | (_.scaled >= 0)])
    def scaled(t):
        return t.select("id", scaled=t.value * scale)

    return src.pipe(scaled).write(DeltaSink(str(path)))


def _rows(path):
    t = DeltaTable(str(path)).to_pyarrow_table()
    return sorted((r["id"], r["scaled"]) for r in t.to_pylist())


def _table(rows):
    return pa.table({"id": [r[0] for r in rows], "value": [r[1] for r in rows]})


def test_a_fired_check_commits_nothing_and_the_next_refresh_takes_the_batch_again(tmp_path):
    src = StaticSource(_table([(1, 1.0)]), name="t")
    node = _sink_node(src, tmp_path / "out")
    assert node.refresh().outcome == "ok"
    before = DeltaTable(str(tmp_path / "out")).version()
    rows_before = _rows(tmp_path / "out")
    # T1: the batch overflows; the sink and the quarantine table stay as they were.
    src.apply(Changes(inserts=_table([(2, 1e200)])))
    held = node.refresh()
    assert held.outcome == "held"
    assert DeltaTable(str(tmp_path / "out")).version() == before
    assert _rows(tmp_path / "out") == rows_before
    assert not (tmp_path / "out_quarantine").exists()
    # T2: the batch no longer fires (the bad row is deleted): it commits, and the sink
    # equals a fresh full run over that version, so nothing was applied twice.
    src.apply(Changes(deletes=_table([(2, 1e200)]), inserts=_table([(3, 2.0)])))
    assert node.refresh().outcome == "ok"
    fresh = _sink_node(StaticSource(_table([(1, 1.0), (3, 2.0)]), name="t"), tmp_path / "fresh")
    assert fresh.refresh().outcome == "ok"
    assert _rows(tmp_path / "out") == _rows(tmp_path / "fresh") == [(1, 1e300), (3, 2e300)]


def test_a_fired_check_leaves_independent_nodes_committing(tmp_path):
    bad = _sink_node(StaticSource(_table([(1, 1e200)]), name="t"), tmp_path / "bad")
    good = _sink_node(StaticSource(_table([(1, 1.0)]), name="t"), tmp_path / "good")
    r = Group([bad, good]).refresh()
    assert r.outcome == "held"
    assert any(s.held is not None and "run-time check" in s.held for s in r.nodes)
    # T3: the other node committed its batch.
    assert _rows(tmp_path / "good") == [(1, 1e300)]

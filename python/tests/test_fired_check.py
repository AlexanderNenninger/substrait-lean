"""A run-time check that fires in a refresh holds the node (ruling 258, #2331).

`fired_check` is the one classifier: the writer's `sverify: ` raise text for
DuckDB, Spark and Snowflake, `RuntimeIssue` for Polars. Anything else is not a
fired check, and a refresh raises it as before.
"""

import duckdb
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify._fired import fired_check
from sverify.errors import UnsupportedError
from sverify.io import StaticSource
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
def test_the_writers_guard_text_is_recognised(engine):
    """The SQL each dialect writes for a guard carries the text its engine
    raises, with the value after the message."""
    d = dialect_of(engine)
    sql = d.raise_("overflow to infinity", "x", "float", "infinite")
    assert "sverify: overflow to infinity: " in sql
    assert fired_check(RuntimeError("Invalid Input Error: sverify: overflow to infinity: inf")) == (
        "overflow to infinity"
    )


def test_polars_raises_a_runtime_issue_that_is_a_fired_check():
    pytest.importorskip("polars")
    from sverify_polars.engine import Overflow

    assert fired_check(Overflow("integer overflow")) == "overflow"
    assert fired_check(ArithmeticError("overflow")) is None

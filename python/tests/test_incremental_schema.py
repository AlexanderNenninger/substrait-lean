"""D46 on a pipeline's reads (#1540, A2): a view's plan is verified for the types
its transform declares, and the rows the view reads must meet them."""

from typing import Any

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify.errors import PreconditionError
from sverify.incremental import Changes, Pipeline


def _view_over(data: pa.Table) -> object:
    con = sv.connect()
    con.put("t", data)
    t = ibis.table({"a": "int32"}, name="t")
    return Pipeline(con).view("v", t.group_by("a").aggregate(n=t.a.count()))


def test_a_view_refuses_a_table_outside_the_declared_width() -> None:
    with pytest.raises(PreconditionError, match=r"column 'a' is declared int32"):
        _view_over(pa.table({"a": pa.array([1, 2**40], pa.int64())}))


def test_a_view_over_a_contained_table_is_built() -> None:
    _view_over(pa.table({"a": pa.array([1, 2], pa.int16())}))


def test_a_batch_outside_the_declared_width_is_refused_and_changes_nothing() -> None:
    """The batch of a refresh goes through the same `_prepare` and `_check_batch`
    as `apply`: refused, with the view's rows and serial unchanged."""
    view: Any = _view_over(pa.table({"a": pa.array([1, 2], pa.int64())}))
    before, serial = sorted(view.rows()), view.serial
    with pytest.raises(PreconditionError, match=r"column 'a' is declared int32"):
        view.apply({"t": Changes(inserts=[(2**40,)])})
    assert (sorted(view.rows()), view.serial) == (before, serial)
    view.apply({"t": Changes(inserts=[(3,)])})
    assert view.serial == serial + 1


def test_a_view_range_checks_a_resident_table() -> None:
    from sverify_duckdb import DuckDBStore

    con = sv.connect()
    con.put("t", DuckDBStore().keep_table(pa.table({"a": pa.array([1, 2**40], pa.int64())})))
    t = ibis.table({"a": "int32"}, name="t")
    with pytest.raises(PreconditionError, match=r"column 'a' is declared int32"):
        Pipeline(con).view("v", t.group_by("a").aggregate(n=t.a.count()))


def test_a_transform_on_a_bound_input_declares_the_tables_own_types() -> None:
    """Nothing to check on a bound input (#1540, A2): the plan's schema there is
    the bound table's, so a value of its physical width is within it."""

    @sv.transform()
    def widen(t):
        return t.select(y=t.a)

    con = sv.connect()
    con.put("t", pa.table({"a": pa.array([1, 2**40], pa.int64())}))
    assert widen(con.table("t")).execute()["y"].tolist() == [1, 2**40]

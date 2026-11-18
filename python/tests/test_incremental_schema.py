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


def test_a_batch_outside_the_declared_width_is_refused() -> None:
    view: Any = _view_over(pa.table({"a": pa.array([1, 2], pa.int64())}))
    with pytest.raises(PreconditionError, match=r"column 'a' is declared int32"):
        view.apply({"t": Changes(inserts=[(2**40,)])})
    view.apply({"t": Changes(inserts=[(3,)])})

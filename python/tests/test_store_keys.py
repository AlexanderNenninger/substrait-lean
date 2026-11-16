"""Keys are an identity boundary (D31, #1511): the store matches them as the
engine's `GROUP BY` does, one zero, one NaN and NULL as its own key, and keeps
the stored values raw."""

from __future__ import annotations

import math
from datetime import datetime

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify._store import by_keys
from sverify.engines import ENGINES
from sverify.incremental import IncrementalView
from sverify.io import Changes

NAN = math.nan


def keys(*vals: float | None) -> pa.Table:
    return pa.table({"k": pa.array(vals, pa.float64())})


def kept(state: pa.Table, *vals: float | None, keep: bool = True) -> list:
    got = by_keys(state, ["k"], keys(*vals), keep=keep)
    return [None if v is None else ("nan" if v != v else v) for v in got.column("k").to_pylist()]


def test_a_nan_key_and_a_null_key_meet() -> None:
    """pyarrow cannot unify per-chunk dictionaries of NaN and NULL (#1511)."""
    state = pa.table({"k": pa.array([NAN, None, 1.0], pa.float64())})
    assert kept(state, None) == [None]
    assert kept(state, NAN) == ["nan"]
    assert kept(state, NAN, None, keep=False) == [1.0]


def test_the_zeros_are_one_key_and_the_state_stays_raw() -> None:
    state = pa.table({"k": pa.array([0.0, -0.0, 1.0], pa.float64())})
    got = by_keys(state, ["k"], keys(-0.0))
    assert got.num_rows == 2
    assert [math.copysign(1.0, v) for v in got.column("k").to_pylist()] == [1.0, -1.0]
    assert by_keys(state, ["k"], keys(0.0), keep=False).column("k").to_pylist() == [1.0]


def test_every_nan_is_one_key() -> None:
    state = pa.table({"k": pa.array([NAN, -NAN, 2.0], pa.float64())})
    assert by_keys(state, ["k"], keys(NAN)).num_rows == 2


T = ibis.table({"ts": "timestamp", "k": "float64"}, name="t")
WHEN = datetime(2024, 1, 1)


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize(
    ("state", "insert", "delete"),
    [
        ([0.0], [-0.0], []),
        ([-0.0], [0.0], []),
        ([0.0, -0.0], [], [-0.0]),
        ([NAN], [None], []),
        ([None], [NAN], []),
        ([NAN, 1.0], [None, 2.0], []),
    ],
)
def test_a_double_key_view_matches_recompute(engine, state, insert, delete) -> None:
    """The six rows of #1511: grouped counts and `DISTINCT`, refreshed after a batch."""
    for query in (
        T.group_by("k").aggregate(n=T.count()),
        T.select("k").distinct(),
    ):
        con = sv.connect()
        con.create("t", T.schema(), [(WHEN, k) for k in state])
        view = IncrementalView(con, query, "v", engine)
        view.apply(
            {"t": Changes(inserts=[(WHEN, k) for k in insert], deletes=[(WHEN, k) for k in delete])}
        )

        def one_zero(rows: list) -> list:
            return sorted(
                repr(tuple(("nan" if v != v else v + 0.0) if isinstance(v, float) else v for v in r))
                for r in rows
            )

        assert one_zero(view.rows()) == one_zero(view.recompute())

"""The parts form of a view's state, over every engine that has it (N14):
a merge writes the change as a part, what reads the table adds the parts up,
and every answer equals the Arrow store's."""

import gc
import os

import pyarrow as pa
import pytest

import sverify as sv
from sverify._arrow_state import ArrowOps
from sverify._parts import MAX_PARTS, PartsState
from sverify._state import Merger
from sverify._weighted import WEIGHT


@pytest.fixture(
    params=[
        pytest.param("polars", marks=pytest.mark.backend("polars")),
        pytest.param("spark", marks=pytest.mark.backend("spark")),
    ]
)
def store(request):
    module = pytest.importorskip(f"sverify_{request.param}.store")
    return getattr(module, f"{request.param.capitalize()}Store")()


def weighted(rows) -> pa.Table:
    return pa.table(
        {
            "k": pa.array([r[0] for r in rows], pa.int64()),
            "s": pa.array([r[1] for r in rows], pa.string()),
            "x": pa.array([r[2] for r in rows], pa.float64()),
            WEIGHT: pa.array([r[3] for r in rows], pa.int64()),
        }
    )


def rows_of(z) -> pa.Table:
    """A handle's rows (a lazy one is computed first)."""
    return z.to_arrow() if hasattr(z, "to_arrow") else z.backend.arrow(z.frame, z.schema)


def bag(t: pa.Table):
    def norm(v):
        return "nan" if isinstance(v, float) and v != v else (0.0 if v == 0 else v)

    return sorted((tuple(norm(v) for v in r.values()) for r in t.to_pylist()), key=repr)


def _merger(store):
    return Merger(sv.connect(None), weighted([]).schema, store)


def test_a_part_is_removed_with_its_last_handle(store):
    z = store.kept(weighted([(1, "a", 1.5, 1)]))
    path = z.parts[0].path
    other = PartsState(z.parts, z.schema, z.backend, consolidated=True)
    assert os.path.isdir(path)
    del z
    gc.collect()
    assert os.path.isdir(path)  # `other` holds it
    del other
    gc.collect()
    assert not os.path.exists(path)


CHANGES = [
    [(1, "a", 1.5, 1), (1, "a", 1.5, 1), (2, "b", 0.0, 1)],  # a row repeated
    [(2, "b", -0.0, -1), (3, None, None, 2)],  # 2 cancels to weight zero
    [(1, "a", 1.5, 1), (4, "c", float("nan"), 1)],  # a row repeated across parts
]


def test_merges_add_parts_and_every_answer_is_the_added_up_table(store):
    """A merge writes the change as a part and runs no plan; what reads the
    table adds the parts up, and equals the Arrow store's."""
    arrow = ArrowOps()
    merge = _merger(store)
    state, expected = store.kept(weighted([])), weighted([])
    for change in CHANGES:
        state = merge(state, weighted(change), keep=True)
        expected = _merger(arrow)(expected, weighted(change))
    assert len(state.parts) == 3 and not state.consolidated
    assert store.has_negative(state) == arrow.has_negative(expected)
    assert bag(rows_of(store.negated(state))) == bag(arrow.negated(expected))
    expanded = store.expanded(state)  # the parts' weights are mixed: added up first
    assert state.consolidated and len(state.parts) == 1
    assert bag(rows_of(expanded)) == bag(arrow.expanded(expected))
    assert bag(state.to_arrow()) == bag(expected)


def test_positive_parts_expand_without_being_added_up(store):
    arrow = ArrowOps()
    merge = _merger(store)
    state = store.kept(weighted([]))
    for change in ([(1, "a", 1.5, 2)], [(1, "a", 1.5, 1), (2, "b", 2.0, 1)]):
        state = merge(state, weighted(change), keep=True)
    expanded = store.expanded(state)
    assert not state.consolidated and len(state.parts) == 2
    assert not store.has_negative(state)
    both = weighted([(1, "a", 1.5, 3), (2, "b", 2.0, 1)])
    assert bag(rows_of(expanded)) == bag(arrow.expanded(both))


def test_key_filters_run_on_the_parts_and_keep_their_state(store):
    arrow = ArrowOps()
    merge = _merger(store)
    state, expected = store.kept(weighted([])), weighted([])
    for change in CHANGES:
        state = merge(state, weighted(change), keep=True)
        expected = _merger(arrow)(expected, weighted(change))
    keys = pa.table({"k": pa.array([1, 2], pa.int64()), "x": pa.array([1.5, 0.0])})
    kept = store.with_keys(state, ["k", "x"], keys)
    assert not kept.consolidated  # as added up as the parts it came from
    assert bag(kept.to_arrow()) == bag(arrow.with_keys(expected, ["k", "x"], keys))
    rest = store.without_keys(state, ["k", "x"], keys)
    assert bag(rest.to_arrow()) == bag(arrow.without_keys(expected, ["k", "x"], keys))


def test_parts_are_added_up_when_the_change_matches_the_base_or_there_are_many(store):
    merge = _merger(store)
    base = store.kept(weighted([(i, "a", 1.5, 1) for i in range(4)]))
    small = merge(base, weighted([(9, "a", 1.5, 1)]), keep=True)
    assert len(small.parts) == 2 and not small.consolidated
    big = merge(small, weighted([(i, "b", 1.5, 1) for i in range(3)]), keep=True)
    assert big.consolidated and len(big.parts) == 1  # 4 pending rows against 4 in the base
    state = store.kept(weighted([(0, "a", 1.5, 1)] * 1000))
    for i in range(MAX_PARTS - 1):
        state = merge(state, weighted([(i, "c", 1.5, 1)]), keep=True)
    assert not state.consolidated and len(state.parts) == MAX_PARTS
    state = merge(state, weighted([(99, "c", 1.5, 1)]), keep=True)
    assert state.consolidated


def test_a_write_that_fails_leaves_no_part_behind(store, monkeypatch):
    from sverify._parts import state_dir

    backend = store.default_backend()
    kept = store.kept(weighted([(1, "a", 1.5, 1)]))
    before = set(os.listdir(state_dir()))
    real = type(backend).write

    def failing(self, frame, schema, path, *, merged=False):
        real(self, frame, schema, path, merged=merged)  # the directory is there, then it fails
        raise RuntimeError("the disk is full")

    monkeypatch.setattr(type(backend), "write", failing)
    merge = _merger(store)
    with pytest.raises(RuntimeError, match="disk is full"):
        merge(kept, weighted([(2, "b", 2.0, 1)]), keep=True)
    gc.collect()
    assert set(os.listdir(state_dir())) == before

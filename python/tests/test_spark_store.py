"""`SparkStore` does what the interim Arrow store does (#173 N6b): each store
operation over generated weighted tables gives the same rows."""

import gc
import os

import pyarrow as pa
import pyarrow.compute as pc
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

from sverify._arrow_state import ArrowOps
from sverify._weighted import WEIGHT

pytestmark = pytest.mark.backend("spark")

spark_store = pytest.importorskip("sverify_spark.store")

ROWS = st.lists(
    st.tuples(
        st.integers(0, 4),
        st.sampled_from(["a", "b", None]),
        st.sampled_from([0.0, -0.0, 1.5, float("nan"), None]),
        st.integers(-2, 3),
    ),
    max_size=10,
)


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
    return z.to_arrow() if hasattr(z, "to_arrow") else spark_store._arrow(z.df, z.schema)


def bag(t: pa.Table):
    def norm(v):
        return "nan" if isinstance(v, float) and v != v else (0.0 if v == 0 else v)

    return sorted((tuple(norm(v) for v in r.values()) for r in t.to_pylist()), key=repr)


@settings(max_examples=8, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(rows=ROWS)
def test_the_operations_agree_with_the_arrow_store(rows):
    arrow, store = ArrowOps(), spark_store.SparkStore()
    z = weighted(rows)
    kept = store.kept(z)
    assert bag(kept.to_arrow()) == bag(z)
    assert store.has_negative(kept) == arrow.has_negative(z)
    assert bag(rows_of(store.negated(kept))) == bag(arrow.negated(z))
    pos = z.filter(pc.call_function("greater", [z[WEIGHT], 0]))
    assert bag(rows_of(store.expanded(store.kept(pos)))) == bag(arrow.expanded(pos))
    keys = pa.table({"k": pa.array([1, 2], pa.int64()), "x": pa.array([0.0, float("nan")])})
    assert bag(rows_of(store.with_keys(kept, ["k", "x"], keys))) == bag(
        arrow.with_keys(z, ["k", "x"], keys)
    )
    assert bag(rows_of(store.without_keys(kept, ["k", "x"], keys))) == bag(
        arrow.without_keys(z, ["k", "x"], keys)
    )


def test_a_part_is_removed_with_its_last_handle():
    store = spark_store.SparkStore()
    z = store.kept(weighted([(1, "a", 1.5, 1)]))
    path = z.parts[0].path
    other = spark_store.SparkState(z.parts, z.schema, z.spark, consolidated=True)
    assert os.path.isdir(path)
    del z
    gc.collect()
    assert os.path.isdir(path)  # `other` holds it
    del other
    gc.collect()
    assert not os.path.exists(path)


def _merger(store):
    import sverify as sv
    from sverify._state import Merger

    con = sv.connect(None)
    return Merger(con, weighted([]).schema, store)


def test_a_weight_sum_past_64_bits_raises_with_ansi_on_or_off():
    """The plan's own guard raises the overflow, whatever the session's ANSI
    mode: a session with `spark.sql.ansi.enabled` off does not wrap the sum."""
    from sverify_spark import engine

    spark = engine.session()
    big = 2**62
    a = weighted([(1, "a", 1.5, big)])
    b = weighted([(1, "a", 1.5, big), (2, "a", 1.5, 1)])
    merge = _merger(spark_store.SparkStore())
    for ansi in ("true", "false"):
        spark.conf.set("spark.sql.ansi.enabled", ansi)
        try:
            with pytest.raises(Exception, match="integer overflow in SUM"):
                merge(a, b)
            assert bag(merge(a, weighted([(2, "a", 1.5, 1)]))) == bag(
                weighted([(1, "a", 1.5, big), (2, "a", 1.5, 1)])
            )
        finally:
            spark.conf.set("spark.sql.ansi.enabled", "true")


CHANGES = [
    [(1, "a", 1.5, 1), (1, "a", 1.5, 1), (2, "b", 0.0, 1)],  # a row repeated
    [(2, "b", -0.0, -1), (3, None, None, 2)],  # 2 cancels to weight zero
    [(1, "a", 1.5, 1), (4, "c", float("nan"), 1)],  # a row repeated across parts
]


def test_merges_add_parts_and_every_answer_is_the_added_up_table():
    """A merge writes the change as a part and runs no plan; what reads the
    table adds the parts up, and equals the Arrow store's."""
    store, arrow = spark_store.SparkStore(), ArrowOps()
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


def test_positive_parts_expand_without_being_added_up():
    store, arrow = spark_store.SparkStore(), ArrowOps()
    merge = _merger(store)
    state = store.kept(weighted([]))
    for change in ([(1, "a", 1.5, 2)], [(1, "a", 1.5, 1), (2, "b", 2.0, 1)]):
        state = merge(state, weighted(change), keep=True)
    expanded = store.expanded(state)
    assert not state.consolidated and len(state.parts) == 2
    assert not store.has_negative(state)
    both = weighted([(1, "a", 1.5, 3), (2, "b", 2.0, 1)])
    assert bag(rows_of(expanded)) == bag(arrow.expanded(both))


def test_key_filters_run_on_the_parts_and_keep_their_state():
    store, arrow = spark_store.SparkStore(), ArrowOps()
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


def test_parts_are_added_up_when_the_change_matches_the_base_or_there_are_many():
    store = spark_store.SparkStore()
    merge = _merger(store)
    base = store.kept(weighted([(i, "a", 1.5, 1) for i in range(4)]))
    small = merge(base, weighted([(9, "a", 1.5, 1)]), keep=True)
    assert len(small.parts) == 2 and not small.consolidated
    big = merge(small, weighted([(i, "b", 1.5, 1) for i in range(3)]), keep=True)
    assert big.consolidated and len(big.parts) == 1  # 4 pending rows against 4 in the base
    state = store.kept(weighted([(0, "a", 1.5, 1)] * 1000))
    for i in range(spark_store.MAX_PARTS - 1):
        state = merge(state, weighted([(i, "c", 1.5, 1)]), keep=True)
    assert not state.consolidated and len(state.parts) == spark_store.MAX_PARTS
    state = merge(state, weighted([(99, "c", 1.5, 1)]), keep=True)
    assert state.consolidated


def test_an_overflow_comes_with_the_read_that_adds_the_parts_up():
    from sverify_spark import engine

    spark = engine.session()
    store = spark_store.SparkStore()
    merge = _merger(store)
    big = 2**62
    for ansi in ("true", "false"):
        spark.conf.set("spark.sql.ansi.enabled", ansi)
        try:
            state = merge(store.kept(weighted([])), weighted([(1, "a", 1.5, big)]), keep=True)
            state = merge(state, weighted([(1, "a", 1.5, big)]), keep=True)
            assert not state.consolidated  # the refresh did not raise
            with pytest.raises(Exception, match="integer overflow in SUM"):
                state.to_arrow()
        finally:
            spark.conf.set("spark.sql.ansi.enabled", "true")

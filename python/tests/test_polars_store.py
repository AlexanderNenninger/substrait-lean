"""`PolarsStore` does what the interim Arrow store does (#173 N6): each store
operation over generated weighted tables gives the same rows."""

import pyarrow as pa
import pyarrow.compute as pc
import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from _arrow_store import ArrowStore
from sverify._weighted import WEIGHT

pytestmark = pytest.mark.backend("polars")

polars_store = pytest.importorskip("sverify_polars.store")

ROWS = st.lists(
    st.tuples(
        st.integers(0, 4),
        st.sampled_from(["a", "b", None]),
        st.sampled_from([0.0, -0.0, 1.5, float("nan"), None]),
        st.integers(-2, 3),
    ),
    max_size=12,
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
    return z.to_arrow() if hasattr(z, "to_arrow") else z.backend.arrow(z.frame, z.schema)


def bag(t: pa.Table):
    def norm(v):
        return "nan" if isinstance(v, float) and v != v else (0.0 if v == 0 else v)

    return sorted((tuple(norm(v) for v in r.values()) for r in t.to_pylist()), key=repr)


@settings(max_examples=25, deadline=None)
@given(rows=ROWS)
def test_the_operations_agree_with_the_arrow_store(rows):
    arrow, store = ArrowStore(), polars_store.PolarsStore()
    z = weighted(rows)
    kept = store.kept(z)
    assert bag(kept.to_arrow()) == bag(z)
    assert store.has_negative(kept) == arrow.has_negative(z)
    assert bag(rows_of(store.negated(kept))) == bag(arrow.negated(z))
    pos = z.filter(pc.call_function("greater", [z[WEIGHT], 0]))
    assert bag(store.expanded(store.kept(pos)).to_arrow()) == bag(arrow.expanded(pos))
    keys = pa.table({"k": pa.array([1, 2], pa.int64()), "x": pa.array([0.0, float("nan")])})
    assert bag(store.with_keys(kept, ["k", "x"], keys).to_arrow()) == bag(
        arrow.with_keys(z, ["k", "x"], keys)
    )
    assert bag(store.without_keys(kept, ["k", "x"], keys).to_arrow()) == bag(
        arrow.without_keys(z, ["k", "x"], keys)
    )


def test_a_weight_sum_that_leaves_64_bits_raises_where_the_parts_are_added_up():
    from sverify_polars.engine import SumOverflow

    store = polars_store.PolarsStore()
    big = 2**63 - 1
    z = store.kept(weighted([(1, "a", 1.5, big), (2, "a", 1.5, 1), (3, "a", 1.5, 1)]))
    plan = _merge_plan(z.schema)
    state = store.merge(plan, z.schema, z, weighted([(1, "a", 1.5, 1)]), keep=True)
    assert not state.consolidated  # the refresh did not raise
    with pytest.raises(SumOverflow):
        state.to_arrow()
    with pytest.raises(SumOverflow):
        store.merge(plan, z.schema, z, weighted([(1, "a", 1.5, 1)]), keep=False)


def _merge_plan(schema: pa.Schema) -> str:
    import sverify as sv
    from sverify._state import Merger

    m = Merger(sv.connect("polars"), schema, ArrowStore())
    plan = m.plan()
    assert plan is not None
    return plan

"""`PolarsStore` does what the interim Arrow store does (#173 N6): each store
operation over generated weighted tables gives the same rows."""

import pyarrow as pa
import pyarrow.compute as pc
import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from sverify._arrow_state import ArrowOps
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
    return z.to_arrow() if hasattr(z, "to_arrow") else z.lf.collect().to_arrow()


def bag(t: pa.Table):
    def norm(v):
        return "nan" if isinstance(v, float) and v != v else (0.0 if v == 0 else v)

    return sorted((tuple(norm(v) for v in r.values()) for r in t.to_pylist()), key=repr)


@settings(max_examples=25, deadline=None)
@given(rows=ROWS)
def test_the_operations_agree_with_the_arrow_store(rows):
    arrow, store = ArrowOps(), polars_store.PolarsStore()
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


def test_a_generation_is_removed_with_its_handle():
    import gc
    import os

    store = polars_store.PolarsStore()
    z = store.kept(weighted([(1, "a", 1.5, 1)]))
    path = z.path
    assert os.path.exists(path)
    del z
    gc.collect()
    assert not os.path.exists(path)

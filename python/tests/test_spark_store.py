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


def test_a_generation_is_removed_with_its_handle():
    store = spark_store.SparkStore()
    z = store.kept(weighted([(1, "a", 1.5, 1)]))
    path = z.path
    assert os.path.isdir(path)
    del z
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

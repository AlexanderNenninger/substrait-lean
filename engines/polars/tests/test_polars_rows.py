"""`rows="multiset"` (#173 N6a): an aggregate run as a bag gives the bag of the
run in `Rel.eval`'s order, on the keys' canonical values (one zero, one NaN),
over tables with NaN, `-0.0`, NULLs and repeated rows. The merge plan of a
state (`sverify._state.Merger`) is one of the plans."""

import math
from collections import Counter
from typing import Literal

import pyarrow as pa
from hypothesis import given, settings
from hypothesis import strategies as st

import sverify as sv
from sverify._state import Merger
from sverify.engine import plan_json, written_plan
from sverify_polars import engine as E

ROWS = st.lists(
    st.tuples(
        st.integers(0, 3),
        st.sampled_from(["a", "b", None]),
        st.sampled_from([0.0, -0.0, 1.5, math.nan, None]),
        st.integers(-2, 3),
    ),
    max_size=14,
)


def table(rows) -> pa.Table:
    return pa.table(
        {
            "k": pa.array([r[0] for r in rows], pa.int64()),
            "s": pa.array([r[1] for r in rows], pa.string()),
            "x": pa.array([r[2] for r in rows], pa.float64()),
            "w": pa.array([r[3] for r in rows], pa.int64()),
        }
    )


def canon(t: pa.Table) -> Counter:
    def key(v):
        if isinstance(v, float):
            return "nan" if v != v else v + 0.0
        return v

    return Counter(tuple(key(v) for v in r.values()) for r in t.to_pylist())


def run(plan: str, tables: dict, rows: Literal["sequence", "multiset"]) -> pa.Table:
    lf = E.to_lazy(plan, tables, rows=rows)
    return E.collect(lf).to_arrow()


@settings(max_examples=40, deadline=None)
@given(rows=ROWS)
def test_an_aggregate_as_a_bag_is_the_aggregate(rows):
    con = sv.connect("polars")
    con.put("t", table(rows))
    t = con.table("t")
    for query in (
        t.group_by(["k", "s", "x"]).aggregate(n=t.w.sum(), c=t.count()),
        t.group_by("x").aggregate(n=t.w.sum()),
        t.group_by(["s", "k"]).aggregate(lo=t.w.min(), hi=t.w.max()),
    ):
        plan = written_plan(plan_json(con, query))
        tables = {"t": table(rows)}
        assert canon(run(plan, tables, "multiset")) == canon(run(plan, tables, "sequence"))


@settings(max_examples=40, deadline=None)
@given(a=ROWS, b=ROWS)
def test_the_merge_plan_as_a_bag_is_the_merge_plan(a, b):
    schema = pa.schema(
        [("k", pa.int64()), ("s", pa.string()), ("x", pa.float64()), ("__weight", pa.int64())]
    )
    plan = Merger(sv.connect("polars"), schema).plan()
    assert plan is not None
    tables = {
        "$merge_a": table(a).rename_columns(schema.names),
        "$merge_b": table(b).rename_columns(schema.names),
    }
    assert canon(run(plan, tables, "multiset")) == canon(run(plan, tables, "sequence"))


def test_only_an_aggregate_reads_the_rows_mode():
    """Only an aggregate reads `rows`: a filter plan is the same either way."""
    con = sv.connect("polars")
    data = table([(1, "a", 1.5, 1)])
    con.put("t", data)
    t = con.table("t")
    plan = written_plan(plan_json(con, t.filter(t.k > 0)))
    tables = {"t": data}
    assert run(plan, tables, "multiset").equals(run(plan, tables, "sequence"))

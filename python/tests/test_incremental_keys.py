"""Differential tests on the key types the delta rules cover: doubles (both
zeros, NaN), decimals, dates and timestamps, NULL keys and duplicate keys.

`test_incremental.py` draws integer and string keys, where bitwise equality
and the reference's equality agree. The store, the merge and the key matching
around the delta plans (`Rel.incremental_sound` proves the plans) are Python;
here a double key's `0.0` and `-0.0`, and its NaNs, are one key (D31, D45), as
a decimal `1.50` and `1.5` are (#1484)."""

from datetime import date, datetime
from decimal import Decimal

import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

import sverify as sv
from _pipelines import canon, random_batch
from sverify.engines import ENGINES
from sverify.incremental import Pipeline

NAN = float("nan")

#: A key type: its Ibis type and the values drawn for it, a few so that keys repeat.
KEYS: dict[str, tuple[str, list]] = {
    "double": ("float64", [0.0, -0.0, NAN, -NAN, 1.5, -1.5, None]),
    "decimal": ("decimal(10, 2)", [Decimal("0.00"), Decimal("1.50"), Decimal("2.25"), None]),
    "date": ("date", [date(1970, 1, 1), date(2020, 2, 29), date(2020, 3, 1), None]),
    "timestamp": (
        "timestamp",
        [datetime(1970, 1, 1), datetime(2020, 2, 29, 12), datetime(2020, 2, 29, 12, 0, 1), None],
    ),
}


#: Views over tables `a(k, v)` and `b(k, w)` in the fragment with delta rules or
#: states per group: the key is joined on, grouped, projected and compared.
def _self_join(a):
    other = a.view()
    return a.join(other, a.k == other.k).select(a.v, other.v.name("v2"))


VIEWS = {
    "join": lambda a, b: a.join(b, a.k == b.k).select(a.v, b.w),
    "self_join": lambda a, b: _self_join(a),
    "project_key": lambda a, b: a.select(a.k, a.v),
    "union": lambda a, b: ibis.union(a.select("k"), b.select("k"), distinct=False),
    "group_by": lambda a, b: a.group_by("k").aggregate(n=a.count(), total=a.v.sum()),
    "distinct": lambda a, b: a.select("k").distinct(),
    "semi_join": lambda a, b: a.semi_join(b, a.k == b.k),
}


SETTINGS = settings(max_examples=12, deadline=None, suppress_health_check=[HealthCheck.too_slow])


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("view", VIEWS)
@pytest.mark.parametrize("key", KEYS)
@SETTINGS
@given(data=st.data())
def test_a_view_over_this_key_matches_its_recomputation(key, view, engine, data):
    ibis_type, values = KEYS[key]
    k = st.sampled_from(values)
    a_row = st.tuples(k, st.one_of(st.none(), st.integers(0, 9)))
    b_row = st.tuples(k, st.sampled_from(["x", "y", None]))
    con = sv.connect()
    con.create(
        "a", ibis.schema({"k": ibis_type, "v": "int64"}), data.draw(st.lists(a_row, max_size=5))
    )
    con.create(
        "b", ibis.schema({"k": ibis_type, "w": "string"}), data.draw(st.lists(b_row, max_size=4))
    )
    pipe = Pipeline(con, engine)
    v = pipe.view("v", VIEWS[view](con.table("a"), con.table("b")))
    assert canon(v.rows()) == canon(v.recompute())
    for _ in range(data.draw(st.integers(1, 3))):
        changes = {
            t: data.draw(random_batch(con, t, a_row if t == "a" else b_row)) for t in v.tables
        }
        pipe.apply(changes)
        assert canon(v.rows()) == canon(v.recompute())

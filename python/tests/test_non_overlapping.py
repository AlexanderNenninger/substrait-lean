"""Non-overlapping ranges (#814): `sv.non_overlapping(lo, hi, by=...)` in
`requires` keeps the left side's keys through a point-in-time join (`Rel.keys`,
`rangedKeys`), and its data check agrees with the pair definition."""

from typing import Literal

import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

import sverify as sv
from sverify.conditions import NonOverlapping
from sverify.io import StaticSource

ORDERS = ibis.table({"order_id": "!int64", "customer_id": "!int64", "ts": "!int64"}, name="orders")
HISTORY = ibis.table(
    {
        "customer_id": "!int64",
        "valid_from": "!int64",
        "valid_to": "int64",
        "city": "string",
    },
    name="history",
)
RANGES = sv.non_overlapping("valid_from", "valid_to", by="customer_id")
UNIQUE_ORDERS = sv.unique("order_id")


def join(predicate, how: Literal["left", "inner"] = "left"):
    return ORDERS.join(HISTORY, predicate(ORDERS, HISTORY), how=how).select(
        ORDERS.order_id, ORDERS.customer_id, HISTORY.city
    )


def point_in_time(o, h):
    """The shop's join: the version valid at the order's time, NULL end open."""
    return (
        (o.customer_id == h.customer_id)
        & (h.valid_from <= o.ts)
        & (h.valid_to.isnull() | (o.ts < h.valid_to))
    )


def proves_unique(query, history_conditions) -> bool:
    report = sv.verify(
        query,
        requires={"orders": [UNIQUE_ORDERS], "history": history_conditions},
        ensures=[sv.unique("order_id")],
    )
    return report.verdict == sv.Verdict.PROVED


@pytest.mark.parametrize("how", ["left", "inner"])
def test_a_point_in_time_join_keeps_the_facts_key(how):
    assert proves_unique(join(point_in_time, how), [RANGES])


def test_without_the_condition_the_key_is_lost():
    assert not proves_unique(join(point_in_time), [])


def test_a_closed_end_has_no_rule():
    """`x <= hi` matches two rows at a boundary `[a, b)`, `[b, c)`."""
    closed = lambda o, h: (  # noqa: E731
        (o.customer_id == h.customer_id)
        & (h.valid_from <= o.ts)
        & (h.valid_to.isnull() | (o.ts <= h.valid_to))
    )
    assert not proves_unique(join(closed), [RANGES])


def test_a_join_that_does_not_equate_the_by_columns_has_no_rule():
    """Versions of other customers match too: the ranges do not apart them."""
    no_customer = lambda o, h: (  # noqa: E731
        (h.valid_from <= o.ts) & (h.valid_to.isnull() | (o.ts < h.valid_to))
    )
    assert not proves_unique(join(no_customer), [RANGES])


def test_ranges_of_other_columns_have_no_rule():
    wrong = sv.non_overlapping("valid_to", "valid_from", by="customer_id")
    assert not proves_unique(join(point_in_time), [wrong])


def test_the_label_and_the_columns_are_named():
    assert RANGES.label == "non_overlapping(valid_from, valid_to, by=[customer_id])"
    assert sv.non_overlapping("a", "b").label == "non_overlapping(a, b)"
    with pytest.raises(ValueError, match="column names"):
        sv.non_overlapping("a", 3)  # type: ignore[arg-type]
    report = sv.verify(
        join(point_in_time), requires={"orders": [UNIQUE_ORDERS], "history": [RANGES]}, ensures=[]
    )
    assert "non_overlapping(valid_from, valid_to, by=[customer_id])" in report.details()


# -- the data check ----------------------------------------------------------


def holds(rows: list[tuple]) -> bool:
    """The definition, on `(k, lo, hi)` rows: every row has a `lo`, and `hi` is
    NULL or at least `lo`; two rows with one `k` (NULLs equal) end where or before
    the other begins, a NULL `hi` satisfying neither side."""
    if any(lo is None or (hi is not None and hi < lo) for _k, lo, hi in rows):
        return False

    def before(a, b):
        return a[2] is not None and a[2] <= b[1]

    return all(
        before(a, b) or before(b, a)
        for i, a in enumerate(rows)
        for j, b in enumerate(rows)
        if i < j and a[0] == b[0]
    )


ROWS = st.lists(
    st.tuples(
        st.sampled_from([None, "a", "b"]),
        st.one_of(st.none(), st.integers(0, 6)),
        st.one_of(st.none(), st.integers(0, 6)),
    ),
    max_size=6,
)
SCHEMA = pa.schema([("k", pa.string()), ("lo", pa.int64()), ("hi", pa.int64())])


@settings(max_examples=60, deadline=None, suppress_health_check=list(HealthCheck))
@given(rows=ROWS)
def test_the_data_check_agrees_with_the_definition(rows):
    cond = sv.non_overlapping("lo", "hi", by="k")
    data = pa.table(
        {c: [r[i] for r in rows] for i, c in enumerate(["k", "lo", "hi"])}, schema=SCHEMA
    )
    # One window query where the table is bound (Ibis's Polars backend has no windows).
    assert (cond.violations(ibis.memtable(data)) == 0) == holds(rows), rows
    assert (
        cond.violating(
            [dict(zip(["k", "lo", "hi"], r, strict=True)) for r in rows], lambda k: k, lambda _: []
        )
        == []
    ) == holds(rows)


def test_a_table_with_no_by_is_one_group():
    cond = sv.non_overlapping("lo", "hi")
    assert isinstance(cond, NonOverlapping) and cond.by == ()
    ok = pa.table({"lo": [1, 5], "hi": [5, None]})
    bad = pa.table({"lo": [1, 4], "hi": [5, None]})
    assert cond.violations(ibis.memtable(ok)) == 0
    assert cond.violations(ibis.memtable(bad)) > 0


def test_incremental_views_refuse_it():
    @sv.transform(requires={"history": [RANGES]})
    def latest(history):
        return history.select(history.customer_id)

    src = StaticSource(
        pa.table({"customer_id": [1], "valid_from": [0], "valid_to": [None], "city": ["x"]}),
        name="history",
    )
    with pytest.raises(ValueError, match="non_overlapping"):
        src.pipe(latest).refresh()


@pytest.mark.parametrize("dtype", ["float64", "string"])
def test_a_range_of_doubles_or_strings_is_refused(dtype):
    t = ibis.table({"k": "!int64", "lo": dtype, "hi": dtype}, name="t")
    with pytest.raises(sv.errors.UnsupportedError, match=r"column 'lo' is .*must be integers"):
        sv.verify(
            t.select(t.k),
            requires={"t": [sv.non_overlapping("lo", "hi", by="k")]},
            ensures=[],
        )


@pytest.mark.parametrize("dtype", ["int32", "decimal(10, 2)", "date", "timestamp", "time"])
def test_ordered_numbers_are_accepted(dtype):
    t = ibis.table({"k": "!int64", "lo": dtype, "hi": dtype}, name="t")
    report = sv.verify(
        t.select(t.k), requires={"t": [sv.non_overlapping("lo", "hi", by="k")]}, ensures=[]
    )
    assert report.verdict is not None


def test_a_range_join_gives_the_output_the_left_sides_row_bound():
    """Single match: the join has at most as many rows as its left side, so a
    cap on the orders bounds it though the history has none."""
    q = join(point_in_time)
    capped = [UNIQUE_ORDERS, sv.max_rows(10)]
    with_ranges = sv.verify(q, requires={"orders": capped, "history": [RANGES]}, ensures=[])
    without = sv.verify(q, requires={"orders": capped, "history": []}, ensures=[])
    assert with_ranges.rows == 10
    assert without.rows is None

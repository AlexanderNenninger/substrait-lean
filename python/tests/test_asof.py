"""ASOF joins: the same results as a reference implementation, Lean's
semantics agree with DataFusion and DuckDB, and the ASOF guarantees are proved."""

import datetime as dt
import json

import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.engine import connect, substrait_json
from sverify.testing import canonical, duckdb_rows, duckdb_sql, inline_tables, lean_rows

INT_SCHEMA = {"device": "int64", "ts": "int64"}
T0 = dt.datetime(2024, 5, 1, 7, 0)


def reference(left, right, tolerance, how):
    """ASOF by definition: per left row, the latest right row of the same
    device at or before it, at most `tolerance` earlier."""
    out = []
    for d, t, a in left:
        matches = [
            r
            for r in right
            if d is not None
            and t is not None
            and r[0] == d
            and r[1] is not None
            and t - tolerance <= r[1] <= t
        ]
        if matches:
            best = max(matches, key=lambda r: r[1])
            out.append((d, t, a, best[1], best[2]))
        elif how == "left":
            out.append((d, t, a, None, None))
    return out


def keyed(value):
    return st.lists(
        st.tuples(
            st.one_of(st.none(), st.integers(0, 2)), st.one_of(st.none(), st.integers(0, 12)), value
        ),
        max_size=10,
        unique_by=lambda r: (r[0], r[1]),
    )


def tables(con, left, right, ts="int64"):
    con.create("acc", ibis.schema({"device": "int64", "ts": ts, "ax": "int64"}), left)
    con.create("gyr", ibis.schema({"device": "int64", "ts": ts, "gx": "int64"}), right)
    return con.table("acc"), con.table("gyr")


@pytest.mark.parametrize("how", ["left", "inner"])
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(left=keyed(st.integers(0, 9)), right=keyed(st.integers(0, 9)))
def test_asof_join_matches_reference(how, left, right):
    con = connect()
    acc, gyr = tables(con, left, right)
    result = sv.asof_join(acc, gyr, on="ts", by="device", tolerance=3, how=how)
    got = [tuple(r.values()) for r in result.to_pyarrow().to_pylist()]
    assert canonical(got) == canonical(reference(left, right, 3, how))


@pytest.mark.parametrize("how", ["left", "inner"])
@settings(
    max_examples=25, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(left=keyed(st.integers(0, 9)), right=keyed(st.integers(0, 9)))
def test_lean_semantics_of_asof_match_duckdb(how, left, right):
    con = connect()
    acc, gyr = tables(con, left, right)
    sql = ibis.to_sql(
        sv.asof_join(acc, gyr, on="ts", by="device", tolerance=3, how=how), dialect="duckdb"
    )
    expected = [tuple(r.values()) for r in duckdb_sql(con, sql).to_pylist()]
    plan = inline_tables(
        json.loads(substrait_json(con, sql, semantics="duckdb")), {"acc": left, "gyr": right}
    )
    lean = lean_rows(json.dumps(plan))
    assert canonical(lean) == canonical(expected)
    assert duckdb_rows(json.dumps(plan)) == lean


acc_t = ibis.table({"device": "int64", "ts": "timestamp", "ax": "float64"}, name="acc")
gyr_t = ibis.table({"device": "int64", "ts": "timestamp", "gx": "float64"}, name="gyr")
TOL = ibis.interval(milliseconds=10)
KEYS = {
    # `ts - tolerance` overflows only at the smallest timestamp: the bound
    # that rules it out is inferred (#244).
    "acc": [sv.unique("device", "ts"), _.device.notnull(), _.ts.notnull()],
    "gyr": [sv.unique("device", "ts")],
}
GUARANTEES = [
    _.ts_right.isnull() | (_.ts_right <= _.ts),
    _.ts_right.isnull() | (_.ts_right >= _.ts - TOL),
]


@pytest.mark.parametrize("how", ["left", "inner"])
def test_asof_guarantees_are_proved(how):
    report = sv.verify(
        sv.asof_join(acc_t, gyr_t, on="ts", by="device", tolerance=TOL, how=how),
        requires=KEYS,
        ensures=GUARANTEES,
        on_inferred="ignore",  # ts - tolerance's bound
    )
    assert report.proved, str(report)


@pytest.mark.slow
def test_ties_on_the_right_keep_the_guarantees():
    """Two gyroscope readings at the same instant: which one is "the latest"
    is up to the engine. The guarantees hold for either pick (D24), and the
    report names the ranking window as the place a rerun may differ."""
    report = sv.verify(
        sv.asof_join(acc_t, gyr_t, on="ts", by="device", tolerance=TOL),
        requires={"acc": KEYS["acc"]},
        ensures=GUARANTEES,
        on_inferred="ignore",
    )
    assert report.proved, str(report)
    assert not report.deterministic
    assert [p.op for p in report._tie_places] == ["window"]


def test_aligning_100hz_with_130hz():
    """An accelerometer at 100 Hz and a gyroscope at 130 Hz: each
    accelerometer sample gets the latest gyroscope sample, at most 10 ms old."""
    con = connect()
    acc = [(1, T0 + dt.timedelta(microseconds=10_000 * i), float(i)) for i in range(100)]
    gyr = [(1, T0 + dt.timedelta(microseconds=round(1e6 * i / 130)), float(i)) for i in range(130)]
    con.create("acc", acc_t.schema(), acc)
    con.create("gyr", gyr_t.schema(), gyr)

    @sv.transform(requires=KEYS, ensures=GUARANTEES, on_inferred="ignore")
    def aligned(acc, gyr):
        return sv.asof_join(acc, gyr, on="ts", by="device", tolerance=TOL)

    rows = aligned(con.table("acc"), con.table("gyr")).to_pyarrow().to_pylist()
    report = aligned.report
    assert report is not None and report.proved
    assert len(rows) == 100
    # The gyroscope samples every 7.7 ms, so every sample finds a partner.
    assert all(r["ts_right"] is not None for r in rows)
    assert max(r["ts"] - r["ts_right"] for r in rows) <= dt.timedelta(milliseconds=10)


def _bound(rows_left: int, rows_right: int, groups: int):
    """Two tables bound to a `sverify.connect()` connection."""
    import pyarrow as pa

    con = connect()
    con.put(
        "l",
        pa.table({"device": [i % groups for i in range(rows_left)], "ts": list(range(rows_left))}),
    )
    con.put(
        "r",
        pa.table(
            {"device": [i % groups for i in range(rows_right)], "ts": list(range(rows_right))}
        ),
    )
    return con.table("l"), con.table("r")


def test_the_pairs_the_join_compares_are_per_by_group():
    import pyarrow as pa

    from sverify.asof import pairs

    left = pa.table({"d": [1, 1, 2, None], "t": [0, 1, 2, 3]})
    right = pa.table({"d": [1, 2, 2, 3, None], "t": [0, 1, 2, 3, 4]})
    assert pairs(left, right, []) == 4 * 5
    assert pairs(left, right, ["d"]) == 2 * 1 + 1 * 2  # NULL and 3 never match


def test_the_join_is_refused_above_the_cap_with_its_exits_named():
    from sverify.errors import UnsupportedError

    left, right = _bound(3000, 3000, 1)
    with pytest.raises(UnsupportedError, match=r"9,000,000 pairs.*`by`.*`max_pairs`") as e:
        sv.asof_join(left, right, on="ts", by="device", max_pairs=1_000_000)
    assert "quadratic" in str(e.value)
    # More `by` groups: fewer pairs, under the cap; and no cap at all.
    left, right = _bound(3000, 3000, 30)
    assert sv.asof_join(left, right, on="ts", by="device", max_pairs=1_000_000) is not None
    left, right = _bound(3000, 3000, 1)
    assert sv.asof_join(left, right, on="ts", by="device", max_pairs=None) is not None


def test_the_default_cap_leaves_the_usual_joins_alone():
    from sverify.asof import MAX_PAIRS

    left, right = _bound(2000, 2000, 1)  # 4 · 10⁶ pairs
    assert MAX_PAIRS > 2000 * 2000
    assert sv.asof_join(left, right, on="ts", by="device") is not None


def test_left_rows_that_share_a_key_each_keep_their_match():
    """#1517: left rows with the same `(by, on)`, a NULL `on` among them, each
    get an output row. The ranking is per left row, so none is dropped."""
    import pyarrow as pa

    con = sv.connect()
    left = {"sym": ["a", "a", "a", "b"], "t": [10, 10, None, 5], "qty": [1, 2, 3, 4]}
    con.put("l", pa.table(left))
    con.put("r", pa.table({"sym": ["a", "a", "b"], "t": [8, 9, 1], "px": [100, 101, 50]}))
    j = sv.asof_join(con.table("l"), con.table("r"), on="t", by="sym")
    report = sv.verify(j, on_inferred="ignore")
    for engine in ("duckdb", "polars"):
        out = report.run(con, engine)
        assert sorted(out.column("qty").to_pylist()) == [1, 2, 3, 4], engine
        qty, px = out.column("qty").to_pylist(), out.column("px").to_pylist()
        rows = dict(zip(qty, px, strict=True))
        assert rows == {1: 101, 2: 101, 3: None, 4: 50}, engine


def test_unique_by_on_is_not_proved_of_the_join():
    """The output has one row per left row, but the key analysis does not carry
    the left table's key through the join and the ranking (#1517): the plan
    no longer claims `unique(by, on)`, with or without the key on `acc`."""
    j = sv.asof_join(acc_t, gyr_t, on="ts", by="device", tolerance=TOL)
    ensures = [sv.unique("device", "ts")]
    requires = {"acc": [_.device.notnull()]}
    assert not sv.verify(j, requires=requires, ensures=ensures, on_inferred="ignore").proved
    assert not sv.verify(j, requires=KEYS, ensures=ensures, on_inferred="ignore").proved

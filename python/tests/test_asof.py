"""ASOF joins: the same results as a reference implementation, Lean's
semantics agree with DataFusion and DuckDB, and the ASOF guarantees are proved."""

import datetime as dt
import json
from collections import Counter

import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.engine import connect, substrait_json
from sverify.testing import canonical, duckdb_rows, duckdb_sql, inline_tables, lean_rows


def pairs(left, right, by) -> int:
    """The pairs of rows an as-of join compares: each left row with every right
    row of its `by` group (rows with a NULL `by` value never match), counted on
    Arrow tables: the rule `AsofSite.pairs` states for the engine's run."""
    if not by:
        return left.num_rows * right.num_rows
    keys = lambda t: [  # noqa: E731
        k for k in zip(*(t[c].to_pylist() for c in by), strict=True) if None not in k
    ]
    right_counts = Counter(keys(right))
    return sum(right_counts[k] for k in keys(left))


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
    assert report.verdict == sv.Verdict.PROVED, str(report)


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
    assert report.verdict == sv.Verdict.PROVED, str(report)
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
    assert report is not None and report.verdict == sv.Verdict.PROVED
    assert len(rows) == 100
    # The gyroscope samples every 7.7 ms, so every sample finds a partner.
    assert all(r["ts_right"] is not None for r in rows)
    assert max(r["ts"] - r["ts_right"] for r in rows) <= dt.timedelta(milliseconds=10)


def _bound(rows_left: int, rows_right: int, groups: int):
    """A connection holding two Arrow tables, and the two tables."""
    import pyarrow as pa

    con = connect()
    for name, n in (("l", rows_left), ("r", rows_right)):
        con.put(name, pa.table({"device": [i % groups for i in range(n)], "ts": list(range(n))}))
    return con, con.table("l"), con.table("r")


def test_the_pairs_the_join_compares_are_per_by_group():
    import pyarrow as pa

    left = pa.table({"d": [1, 1, 2, None], "t": [0, 1, 2, 3]})
    right = pa.table({"d": [1, 2, 2, 3, None], "t": [0, 1, 2, 3, 4]})
    assert pairs(left, right, []) == 4 * 5
    assert pairs(left, right, ["d"]) == 2 * 1 + 1 * 2  # NULL and 3 never match


def _pairs_on_run(con, report, engine="duckdb") -> list[int]:
    """The checker's count of each as-of join's pairs (`AsofSite.pairs`), run."""
    from sverify.engine import run_plan, written_plan

    return [
        int(run_plan(con, written_plan(json.dumps(c["plan"])), engine).column(0)[0].as_py() or 0)
        for c in report._asof_checks
    ]


@settings(max_examples=30, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(
    left=st.lists(
        st.tuples(st.one_of(st.none(), st.integers(0, 2)), st.integers(0, 9)), max_size=8
    ),
    right=st.lists(
        st.tuples(st.one_of(st.none(), st.integers(0, 3)), st.integers(0, 9)), max_size=8
    ),
    by=st.booleans(),
)
def test_the_checkers_count_is_the_arrow_rule(left, right, by):
    """`AsofSite.pairs`, the plan a run evaluates, counts what `asof.pairs`
    counts on Arrow tables: one rule (ruling 162 A7)."""
    import pyarrow as pa

    con = connect()
    ts = {
        n: pa.table(
            {"device": [r[0] for r in rs], "ts": [r[1] for r in rs]},
            schema=pa.schema([("device", pa.int64()), ("ts", pa.int64())]),
        )
        for n, rs in (("l", left), ("r", right))
    }
    for n, t in ts.items():
        con.put(n, t)
    report = sv.verify(
        sv.asof_join(con.table("l"), con.table("r"), on="ts", by="device" if by else ())
    )
    assert _pairs_on_run(con, report) == [pairs(ts["l"], ts["r"], ["device"] if by else [])]


def test_the_run_is_refused_above_the_cap_with_its_exits_named():
    from sverify.errors import UnsupportedError

    con, left, right = _bound(1000, 1000, 1)
    report = sv.verify(sv.asof_join(left, right, on="ts", by="device", max_pairs=100_000))
    with pytest.raises(UnsupportedError, match=r"1,000,000 pairs.*`by`.*`max_pairs`") as e:
        report.run(con, "polars")
    assert "quadratic" in str(e.value)
    # DuckDB writes the join as its ASOF JOIN, which compares no pairs: no cap.
    assert report.run(con, "duckdb").num_rows == 1000
    # With a tolerance it keeps the range join, and the cap.
    tol = sv.verify(
        sv.asof_join(left, right, on="ts", by="device", tolerance=5, max_pairs=100_000),
        on_inferred="ignore",
    )
    with pytest.raises(UnsupportedError, match=r"1,000,000 pairs"):
        tol.run(con, "duckdb")
    # More `by` groups: fewer pairs, under the cap; and no cap at all.
    con, left, right = _bound(1000, 1000, 20)
    sv.verify(sv.asof_join(left, right, on="ts", by="device", max_pairs=100_000)).run(con, "duckdb")
    con, left, right = _bound(1000, 1000, 1)
    sv.verify(sv.asof_join(left, right, on="ts", by="device", max_pairs=None)).run(con, "duckdb")


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_the_cap_holds_on_tables_read_from_files(tmp_path, engine):
    """Before #1447's A7 the cap counted Arrow tables only: a join over files
    ran with no bound. The count now runs on the engine, over the files."""
    import pyarrow as pa
    import pyarrow.parquet as pq

    from sverify._scan import Scan
    from sverify.errors import UnsupportedError

    con = connect()
    schema = pa.schema([("device", pa.int64()), ("ts", pa.int64())])
    for name in ("l", "r"):
        f = tmp_path / f"{name}.parquet"
        pq.write_table(pa.table({"device": [0] * 1000, "ts": list(range(1000))}, schema=schema), f)
        con.put(name, Scan((str(f),), schema))
    # A tolerance keeps DuckDB on the range join; Polars has no native as-of join.
    report = sv.verify(
        sv.asof_join(
            con.table("l"), con.table("r"), on="ts", by="device", tolerance=5, max_pairs=100_000
        ),
        on_inferred="ignore",
    )
    with pytest.raises(UnsupportedError, match=r"1,000,000 pairs"):
        report.run(con, engine)


def test_the_default_cap_leaves_the_usual_joins_alone():
    from sverify.asof import MAX_PAIRS

    con, left, right = _bound(2000, 2000, 1)  # 4 · 10⁶ pairs
    assert MAX_PAIRS > 2000 * 2000
    sv.verify(sv.asof_join(left, right, on="ts", by="device")).run(con, "duckdb")


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


@pytest.mark.parametrize("how", ["left", "inner"])
def test_a_left_key_is_a_key_of_the_join(how):
    """At most one output row per left row (#1992): the ranking keeps one row
    per numbered left row, and a key of the left table determines that number,
    so the left key is a key of the output. Without it nothing is claimed."""
    j = sv.asof_join(acc_t, gyr_t, on="ts", by="device", tolerance=TOL, how=how)
    ensures = [sv.unique("device", "ts")]
    requires = {"acc": [_.device.notnull()]}
    assert (
        sv.verify(j, requires=requires, ensures=ensures, on_inferred="ignore").verdict
        == sv.Verdict.UNPROVED
    )
    assert (
        sv.verify(j, requires=KEYS, ensures=ensures, on_inferred="ignore").verdict
        == sv.Verdict.PROVED
    )


@pytest.mark.parametrize("how", ["left", "inner"])
def test_a_left_key_off_the_join_columns_survives(how):
    """The issue's shape: facts keyed on `order_id`, a dimension keyed on
    `(customer_id, ts)`; `unique(order_id)` holds after the as-of join."""
    orders = ibis.table(
        {"order_id": "int64", "customer_id": "int64", "ts": "int64", "qty": "int64"}, name="orders"
    )
    tiers = ibis.table({"customer_id": "int64", "ts": "int64", "tier": "string"}, name="tiers")
    j = sv.asof_join(orders, tiers, on="ts", by="customer_id", how=how)
    report = sv.verify(
        j,
        requires={
            "orders": [sv.unique("order_id")],
            "tiers": [sv.unique("customer_id", "ts")],
        },
        ensures=[sv.unique("order_id")],
        on_inferred="ignore",
    )
    assert report.verdict == sv.Verdict.PROVED, str(report)


@pytest.mark.parametrize(
    "sql",
    [
        "SELECT l.device, l.ts, r.ts AS rts FROM l ASOF LEFT JOIN r"
        " ON l.device = r.device AND l.ts >= r.ts",
        "SELECT l.ts, r.ts AS rts FROM l ASOF JOIN r ON l.ts >= r.ts",
    ],
)
def test_the_lifts_asof_join_is_an_as_of_site_too(sql):
    """The checker reads DuckDB's `ASOF JOIN`, as the lift writes it, as an
    as-of join (`Rel.asofSite`, ruling 162 A2); its count is the Arrow rule's.
    A SQL query states no `max_pairs`, so its run has no cap yet."""
    con, _, _ = _bound(30, 40, 3)
    schema = ibis.schema({"device": "int64", "ts": "int64"})
    report = sv.verify(sql, tables={"l": schema, "r": schema})
    by = ["device"] if "device =" in sql else []
    assert _pairs_on_run(con, report) == [pairs(con.get("l"), con.get("r"), by)]
    assert report._asof_max_pairs is None


NATIVE_KINDS = {
    "int": ("int64", lambda i: i),
    "date": ("date", lambda i: dt.date(2024, 1, 1) + dt.timedelta(days=i)),
    "timestamp": ("timestamp", lambda i: dt.datetime(2024, 1, 1) + dt.timedelta(hours=i)),
    "string": ("string", lambda i: f"t{i:02d}"),
}


def _asof_tables(con, kind, left, right):
    """`l(k, t, id)` and `r(k, t, v)` with `t` of the kind; rows are `(k, t, id)`
    and `(k, t, v)` with `t` an int or None."""
    ty, f = NATIVE_KINDS[kind]
    conv = lambda rows: [(k, None if t is None else f(t), x) for k, t, x in rows]  # noqa: E731
    con.create("l", ibis.schema({"k": "int64", "t": ty, "id": "int64"}), conv(left))
    con.create("r", ibis.schema({"k": "int64", "t": ty, "v": "int64"}), conv(right))
    return con.table("l"), con.table("r"), f


def _enc(v):
    """A value as Lean reads it: a date is its day, a timestamp its microseconds."""
    if isinstance(v, dt.datetime):
        return (v - dt.datetime(1970, 1, 1)) // dt.timedelta(microseconds=1)
    if isinstance(v, dt.date):
        return (v - dt.date(1970, 1, 1)).days
    return v


def _lean_allowed(expr, kind, left, right):
    """The rows `Rel.eval` allows for each left row: its output over each choice
    among the tied latest right rows (variant `j` keeps the `j`-th row of every
    group of right rows that share `(k, t)`), by left id."""
    from sverify.ibis_substrait import to_substrait_json

    f = NATIVE_KINDS[kind][1]
    plan = json.loads(to_substrait_json(expr))
    groups: dict = {}
    for r in right:
        groups.setdefault((r[0], r[1]), []).append(r)
    allowed: dict[int, set] = {}
    for j in range(max([len(g) for g in groups.values()], default=1)):
        kept = [g[j % len(g)] for g in groups.values()]
        enc = lambda rows: [(k, _enc(None if t is None else f(t)), x) for k, t, x in rows]  # noqa: E731
        rows = inline_tables(plan, {"l": enc(left), "r": enc(kept)})
        for out in lean_rows(json.dumps(rows)):
            allowed.setdefault(out[2], set()).add(out)
    return allowed


@pytest.mark.parametrize("kind", NATIVE_KINDS)
@pytest.mark.parametrize("how", ["left", "inner"])
@settings(
    max_examples=15, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(
    left=st.lists(
        st.tuples(st.one_of(st.none(), st.integers(0, 2)), st.one_of(st.none(), st.integers(0, 6))),
        max_size=8,
    ),
    right=st.lists(
        st.tuples(st.one_of(st.none(), st.integers(0, 2)), st.one_of(st.none(), st.integers(0, 6))),
        max_size=8,
    ),
)
def test_duckdbs_asof_join_gives_a_row_the_plan_allows(kind, how, left, right):
    """DuckDB runs the as-of join as its ASOF JOIN (ruling 162, #1447 item 6):
    each left row, equal ones included, keeps one latest right row whole; NULL
    keys and NULL times never match. The rows are `Rel.eval`'s: equal where
    `(by, on)` is unique on the right, and one of the rows its choices among
    tied right rows give (A5, A6)."""
    left = [(k, t, i) for i, (k, t) in enumerate(left)]
    right = [(k, t, 100 + i) for i, (k, t) in enumerate(right)]
    con = connect()
    lt, rt, _ = _asof_tables(con, kind, left, right)
    expr = sv.asof_join(lt, rt, on="t", by="k", how=how, max_pairs=0)
    report = sv.verify(expr)
    # `max_pairs=0` refuses any count: the run is native, or it raises.
    assert [c["form"] for c in report._asof_checks] == ["builder"]
    out = [tuple(_enc(v) for v in r.values()) for r in report.run(con, "duckdb").to_pylist()]
    allowed = _lean_allowed(expr, kind, left, right)
    assert sorted(r[2] for r in out) == sorted(allowed)
    for row in out:
        assert row in allowed[row[2]], row


def test_the_native_sql_is_an_asof_join_where_the_site_is_plain():
    """A plain site is written as `ASOF [LEFT] JOIN`; a tolerance, a double
    time (A3: NaN and the zeros are not probed) and a plan rewritten to run
    keep the range join."""
    from sverify.engine import written_plan
    from sverify.sql import to_sql

    def sql(j):
        report = sv.verify(j, on_inferred="ignore")
        assert report.internal_plan is not None
        plan = json.loads(written_plan(report.internal_plan))
        return to_sql(plan, "duckdb", asof=report._asof_checks)

    con = connect()
    lt, rt, _ = _asof_tables(con, "int", [(1, 5, 1)], [(1, 4, 100)])
    assert "ASOF LEFT JOIN" in sql(sv.asof_join(lt, rt, on="t", by="k"))
    assert "ASOF JOIN" in sql(sv.asof_join(lt, rt, on="t", by="k", how="inner"))
    assert "ASOF" not in sql(sv.asof_join(lt, rt, on="t", by="k", tolerance=2))
    con.create("fl", ibis.schema({"k": "int64", "t": "float64"}), [(1, 5.0)])
    con.create("fr", ibis.schema({"k": "int64", "t": "float64"}), [(1, 4.0)])
    assert "ASOF" not in sql(sv.asof_join(con.table("fl"), con.table("fr"), on="t", by="k"))


@pytest.mark.parametrize("how", ["left", "inner"])
def test_the_lift_of_the_native_sql_is_the_same_site(how):
    """Round trip (A6): the lift reads the ASOF JOIN the writer emits as an
    as-of site of the same keys, `on` columns and join type."""
    from sverify.engine import written_plan
    from sverify.sql import to_sql

    con = connect()
    lt, rt, _ = _asof_tables(con, "int", [(1, 5, 1)], [(1, 4, 100)])
    report = sv.verify(sv.asof_join(lt, rt, on="t", by="k", how=how))
    assert report.internal_plan is not None
    sql = to_sql(
        json.loads(written_plan(report.internal_plan)),
        "duckdb",
        asof=report._asof_checks,
        rows="multiset",
    )
    assert "ASOF" in sql
    schema = {"k": "int64", "t": "int64"}
    lifted = sv.verify(
        sql,
        tables={
            "l": ibis.schema({**schema, "id": "int64"}),
            "r": ibis.schema({**schema, "v": "int64"}),
        },
    )
    (a,), (b,) = report._asof_checks, lifted._asof_checks
    assert (b["form"], a["form"]) == ("lift", "builder")
    assert {x: a[x] for x in ("keys", "lon", "ron", "outer")} == {
        x: b[x] for x in ("keys", "lon", "ron", "outer")
    }


def test_the_native_join_runs_over_files_with_no_count(tmp_path):
    """Verdict 2 of ruling 162: a join over a Parquet scan had no bound. On DuckDB
    it is an ASOF JOIN now, which compares no pairs, so a small `max_pairs`
    neither counts nor refuses."""
    import pyarrow as pa
    import pyarrow.parquet as pq

    from sverify._scan import Scan

    con = connect()
    schema = pa.schema([("device", pa.int64()), ("ts", pa.int64())])
    for name in ("l", "r"):
        f = tmp_path / f"{name}.parquet"
        pq.write_table(pa.table({"device": [0] * 1000, "ts": list(range(1000))}, schema=schema), f)
        con.put(name, Scan((str(f),), schema))
    report = sv.verify(
        sv.asof_join(con.table("l"), con.table("r"), on="ts", by="device", max_pairs=100)
    )
    assert report.run(con, "duckdb").num_rows == 1000


def _ranked_asof(left, right, keep):
    """`asof_join`'s plan with its last filter replaced: `keep(rank)` over the
    rank (0 for the latest right row), so `rank <= 1` keeps two matches."""
    from sverify.asof import RANK, ROW

    left = left.mutate(**{ROW: ibis.row_number().over(order_by=[left["k"], left["t"]])})
    joined = left.join(right, [left["k"] == right["k"], right["t"] <= left["t"]], how="left")
    latest = ibis.window(group_by=[joined[ROW]], order_by=ibis.desc(joined["t_right"]))
    ranked = joined.mutate(**{RANK: ibis.row_number().over(latest)})
    return ranked.filter(keep(ranked[RANK])).drop(ROW, RANK, "k_right")


def _agree_with_the_range_join(expr, con):
    report = sv.verify(expr, on_inferred="ignore")
    native = report.run(con, "duckdb").to_pylist()
    other = report.run(con, "polars").to_pylist()
    assert canonical([tuple(r.values()) for r in native]) == canonical(
        [tuple(r.values()) for r in other]
    )
    return native


@pytest.mark.parametrize(
    "above",
    [
        lambda j: j.filter(j.v > 100),
        lambda j: j.filter(j.v.isnull()),
        lambda j: j.mutate(w=j.v + 1).filter(j.id > 1),
    ],
    ids=["filter v", "filter null", "mutate and filter"],
)
def test_a_filter_above_an_asof_join_is_not_dropped(above):
    """A filter on the join's output stays: the site is the join, and what the
    plan does above it is not the native join's to drop."""
    con = connect()
    lt, rt, _ = _asof_tables(
        con, "int", [(1, 5, 1), (1, 9, 2), (2, 7, 3)], [(1, 4, 100), (1, 8, 101), (2, 6, 102)]
    )
    _agree_with_the_range_join(above(sv.asof_join(lt, rt, on="t", by="k")), con)


def test_a_ranking_that_keeps_more_than_the_latest_row_is_not_native():
    """`rank <= 1` keeps the two latest right rows per left row: no ASOF JOIN
    returns that, so the plan keeps the range join."""
    con = connect()
    lt, rt, _ = _asof_tables(
        con, "int", [(1, 9, 1), (1, 5, 2)], [(1, 4, 100), (1, 8, 101), (1, 7, 102)]
    )
    out = _agree_with_the_range_join(_ranked_asof(lt, rt, lambda r: r <= 1), con)
    assert len(out) == 3


def test_a_report_read_back_keeps_the_as_of_checks_and_the_cap():
    """#1863: JSON keeps the pair counts and the cap; an exported plan, read
    back by `from_substrait`, keeps the cap, so its run is refused above it."""
    from sverify.errors import UnsupportedError

    con, left, right = _bound(1000, 1000, 1)
    report = sv.verify(sv.asof_join(left, right, on="ts", by="device", max_pairs=100_000))
    assert report._asof_checks and report._asof_max_pairs == 100_000
    back = sv.Report.from_json(report.to_json())
    assert back._asof_checks == report._asof_checks
    assert back._asof_max_pairs == 100_000
    again = sv.Report.from_substrait(report.to_substrait())
    assert again._asof_max_pairs == 100_000
    # DuckDB writes the join natively and takes no count; Polars counts.
    with pytest.raises(UnsupportedError, match=r"1,000,000 pairs"):
        again.run(con, "polars")

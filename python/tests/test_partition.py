"""Sharded evaluation (`sverify.partition`, `SubstraitLean/Partition.lean`):
the combined result of a plan run shard by shard equals its result on all
the data, and plans whose result would depend on the split are refused."""

import json
import math
from collections.abc import Sequence

import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, assume, given, settings
from hypothesis import strategies as st

import sverify as sv
from sverify import polars_engine
from sverify.engine import connect, run_plan, substrait_json, written_plan
from sverify.ibis_substrait import to_substrait_json
from sverify.partition import NotShardable, apriori_tolerance, run_sharded, split
from sverify.testing import canonical

pytestmark = pytest.mark.backend("polars")

#: Doubles within the split's proved bound (`run_sharded`'s `reproducible`).
PLAN = sv.equivalent(floats="plan")

R = ibis.schema({"a": "int64", "b": "int64", "c": "int64"})
S = ibis.schema({"b": "int64", "d": "string"})
Q = ibis.schema({"b": "int64", "e": "int64"})
S_ROWS = [(0, "zero"), (1, "one"), (2, "two"), (2, "deux")]

LINEAR = [
    "SELECT a, b + 1 AS x FROM r WHERE a > 0",
    "SELECT r.a, s.d FROM r JOIN s ON r.b = s.b",
    "SELECT r.a, s.d FROM r LEFT JOIN s ON r.b = s.b",
    "SELECT a FROM r WHERE b IN (SELECT b FROM s)",
]
TWO_PHASE = [
    "SELECT b, COUNT(*) AS n, SUM(a) AS s, MIN(c) AS lo, MAX(c) AS hi FROM r GROUP BY b",
    "SELECT COUNT(a) AS n, SUM(a) AS s, MAX(c) AS hi FROM r",
    "SELECT b, SUM(a) * 2 AS s2 FROM r WHERE c > 0 GROUP BY b HAVING SUM(a) > 3",
    "SELECT s.d, COUNT(*) AS n, MIN(r.a) AS lo FROM r JOIN s ON r.b = s.b GROUP BY s.d",
    "SELECT b, MIN(DISTINCT c) AS lo, MAX(DISTINCT a) AS hi FROM r GROUP BY b",
]
#: With `r` split on `b`: (query, mode).
KEYED = [
    ("SELECT b, COUNT(DISTINCT a) AS n, SUM(DISTINCT c) AS s FROM r GROUP BY b", "linear"),
    ("SELECT DISTINCT b, a FROM r", "linear"),
    ("SELECT b, n FROM (SELECT b, a, COUNT(*) AS n FROM r GROUP BY b, a) t WHERE n > 1", "linear"),
    ("SELECT x, COUNT(*) AS k FROM (SELECT DISTINCT b AS x, c FROM r) t GROUP BY x", "linear"),
    ("SELECT COUNT(DISTINCT b) AS n, SUM(DISTINCT b) AS s FROM r", "two_phase"),
    ("SELECT c, COUNT(DISTINCT b) AS n FROM r GROUP BY c", "two_phase"),
]
KEYED_REFUSED = [
    ("SELECT COUNT(DISTINCT a) AS n FROM r", "unless its argument is the split key"),
    ("SELECT DISTINCT a FROM r", "include the split key"),
    ("SELECT b, SUM(CAST(a AS DOUBLE)) AS s FROM r GROUP BY b", "not associative"),
]
#: Sums of doubles, split only with `float_order="any"`.
FLOATS = [
    "SELECT b, SUM(CAST(a AS DOUBLE)) AS s, AVG(CAST(c AS DOUBLE)) AS m, COUNT(*) AS n"
    " FROM r GROUP BY b",
    "SELECT AVG(CAST(a AS DOUBLE)) AS m FROM r",
]
REFUSED = [
    ("SELECT AVG(CAST(a AS DOUBLE)) AS m FROM r", "not associative"),
    ("SELECT COUNT(DISTINCT a) AS n FROM r", "DISTINCT values"),
    ("SELECT x.a FROM r AS x JOIN r AS y ON x.b = y.b", "co-partitioning"),
    ("SELECT a FROM r ORDER BY a LIMIT 3", "FETCH"),
    ("SELECT a, ROW_NUMBER() OVER (PARTITION BY b ORDER BY a) AS k FROM r", "window"),
]

SETTINGS = settings(
    max_examples=20,
    deadline=None,
    suppress_health_check=[HealthCheck.function_scoped_fixture, HealthCheck.too_slow],
)


def plan_of(sql: str) -> str:
    con = connect()
    con.create("r", R)
    con.create("s", S)
    con.create("q", Q)
    return substrait_json(con, sql, semantics="duckdb")


def reference(plan: str, rows: list[tuple], q_rows: Sequence[tuple] = ()) -> list[str]:
    """The plan on all the data, on Polars."""
    con = connect()
    con.create("r", R, rows)
    con.create("s", S, S_ROWS)
    con.create("q", Q, list(q_rows))
    got = run_plan(con, written_plan(plan), "polars")
    return canonical(tuple(r.values()) for r in got.to_pylist())


def arrow(rows: list[tuple]) -> pa.Table:
    return pa.table({n: pa.array([r[i] for r in rows], pa.int64()) for i, n in enumerate("abc")})


small = st.integers(-3, 3)
r_rows = st.lists(st.tuples(small, st.integers(0, 3), small | st.none()), max_size=12)
#: Rows of `r`, and the shard (of 4) each one goes to.
rows_and_shards = r_rows.flatmap(
    lambda rows: st.tuples(
        st.just(rows), st.lists(st.integers(0, 3), min_size=len(rows), max_size=len(rows))
    )
)


@pytest.mark.parametrize("sql", LINEAR + TWO_PHASE)
@SETTINGS
@given(data=rows_and_shards)
def test_sharded_equals_whole(sql: str, data):
    rows, where = data
    plan = plan_of(sql)
    pairs = list(zip(rows, where, strict=True))
    shards = [{"r": arrow([row for row, k in pairs if k == i])} for i in range(4)]
    s_table = pa.table({"b": [b for b, _ in S_ROWS], "d": [d for _, d in S_ROWS]})
    got = run_sharded(plan, shards, sharded=["r"], broadcast={"s": s_table})
    assert canonical(tuple(r.values()) for r in got.to_pylist()) == reference(plan, rows)


@pytest.mark.parametrize("sql", LINEAR)
def test_linear_plans_are_concatenated(sql: str):
    s = split(plan_of(sql), ["r"])
    assert s.mode == "linear"
    assert "__partials" in json.dumps(s.combine)


@pytest.mark.parametrize("sql", TWO_PHASE)
def test_aggregates_run_in_two_phases(sql: str):
    assert split(plan_of(sql), ["r"]).mode == "two_phase"


@pytest.mark.parametrize(("sql", "why"), REFUSED)
def test_refused_with_a_reason(sql: str, why: str):
    with pytest.raises(NotShardable, match=why):
        split(plan_of(sql), ["r"])


@pytest.mark.parametrize(("sql", "mode"), KEYED)
@SETTINGS
@given(rows=r_rows)
def test_split_keys(sql: str, mode: str, rows):
    """Shard `i` holds the rows with `b = i`."""
    plan = plan_of(sql)
    s = split(plan, ["r"], keys={"r": ["b"]})
    assert (s.mode, s.proved) == (mode, True)
    shards = [{"r": arrow([row for row in rows if row[1] == i])} for i in range(4)]
    got = run_sharded(plan, shards, sharded=["r"], keys={"r": ["b"]})
    assert canonical(tuple(r.values()) for r in got.to_pylist()) == reference(plan, rows)


@pytest.mark.parametrize(("sql", "why"), KEYED_REFUSED)
def test_split_keys_refuse_the_rest(sql: str, why: str):
    with pytest.raises(NotShardable, match=why):
        split(plan_of(sql), ["r"], keys={"r": ["b"]})


def test_split_keys_are_checked_on_the_data():
    plan = plan_of("SELECT DISTINCT b, a FROM r")
    shards = [{"r": arrow([(1, 2, 0)])}, {"r": arrow([(1, 2, 0), (3, 1, 0)])}]
    with pytest.raises(ValueError, match=r"split key \(2,\) .* on shards 0 and 1"):
        run_sharded(plan, shards, sharded=["r"], keys={"r": ["b"]})


@pytest.mark.parametrize("sql", FLOATS)
@SETTINGS
@given(data=rows_and_shards)
def test_float_order_any(sql: str, data):
    """Within a bound (`test_sharded_doubles_within_the_reported_tolerance`),
    and small integers add exactly as doubles, so here the result is
    Lean's."""
    rows, where = data
    plan = plan_of(sql)
    with pytest.raises(NotShardable, match="not associative"):
        split(plan, ["r"])
    assert not split(plan, ["r"], float_order="any").proved
    pairs = list(zip(rows, where, strict=True))
    shards = [{"r": arrow([row for row, k in pairs if k == i])} for i in range(4)]
    got = run_sharded(plan, shards, sharded=["r"], reproducible=PLAN)
    assert canonical(tuple(r.values()) for r in got.to_pylist()) == reference(plan, rows)


#: `r` and `q` both split on `b` (co-partitioned).
CO_PARTITIONED = [
    "SELECT r.a, q.e FROM r JOIN q ON r.b = q.b",
    "SELECT r.a, q.e FROM r LEFT JOIN q ON r.b = q.b AND r.a < q.e",
    "SELECT a FROM r WHERE b IN (SELECT b FROM q)",
    "SELECT r.b, COUNT(*) AS n, SUM(q.e) AS s FROM r JOIN q ON r.b = q.b GROUP BY r.b",
]


def q_arrow(rows: list[tuple]) -> pa.Table:
    return pa.table({n: pa.array([r[i] for r in rows], pa.int64()) for i, n in enumerate("be")})


@pytest.mark.parametrize("sql", CO_PARTITIONED)
@SETTINGS
@given(rows=r_rows, q_rows=st.lists(st.tuples(st.integers(0, 3), small), max_size=8))
def test_co_partitioned_joins(sql: str, rows, q_rows):
    plan = plan_of(sql)
    keys = {"r": ["b"], "q": ["b"]}
    assert split(plan, ["r", "q"], keys=keys).mode == "linear"
    shards = [
        {"r": arrow([x for x in rows if x[1] == i]), "q": q_arrow([y for y in q_rows if y[0] == i])}
        for i in range(4)
    ]
    got = run_sharded(plan, shards, sharded=["r", "q"], keys=keys)
    assert canonical(tuple(r.values()) for r in got.to_pylist()) == reference(plan, rows, q_rows)


def test_joins_on_other_columns_are_not_co_partitioned():
    with pytest.raises(NotShardable, match="co-partitioning"):
        split(
            plan_of("SELECT r.a FROM r JOIN q ON r.a = q.e"),
            ["r", "q"],
            keys={"r": ["b"], "q": ["b"]},
        )


WINDOWS = [
    "SELECT a, b, ROW_NUMBER() OVER (PARTITION BY b ORDER BY a) AS k FROM r",
    "SELECT a, b, LAG(c, 1) OVER (PARTITION BY b ORDER BY a) AS prev FROM r",
]
#: Rows of `r` with no two equal on `(a, b)`.
unique_rows = st.lists(
    st.tuples(small, st.integers(0, 3), small | st.none()), max_size=12, unique_by=lambda r: r[:2]
)


@pytest.mark.parametrize("sql", WINDOWS)
@SETTINGS
@given(rows=unique_rows)
def test_windows_on_the_split_key(sql: str, rows):
    plan = plan_of(sql)
    with pytest.raises(NotShardable, match="window"):
        split(plan, ["r"], keys={"r": ["b"]})
    unique = {"r": [["a", "b"]]}
    assert split(plan, ["r"], keys={"r": ["b"]}, unique=unique).mode == "linear"
    shards = [{"r": arrow([x for x in rows if x[1] == i])} for i in range(4)]
    got = run_sharded(plan, shards, sharded=["r"], keys={"r": ["b"]}, unique=unique)
    assert canonical(tuple(r.values()) for r in got.to_pylist()) == reference(plan, rows)


def test_unique_is_checked_on_the_data():
    plan = plan_of(WINDOWS[0])
    shards = [{"r": arrow([(1, 2, 0), (1, 2, 5)])}]
    with pytest.raises(ValueError, match="two rows"):
        run_sharded(plan, shards, sharded=["r"], keys={"r": ["b"]}, unique={"r": [["a", "b"]]})


def test_broadcast_tables_are_not_split():
    """A plan that reads only broadcast tables would be repeated on every shard."""
    with pytest.raises(NotShardable, match="no sharded table"):
        split(plan_of("SELECT b FROM s"), ["r"])


def test_partial_sum_may_overflow_where_the_total_does_not():
    """Integer sums are checked in each phase: shards of large values of
    opposite signs fail instead of giving a wrong result."""
    plan = plan_of("SELECT SUM(a) AS s FROM r")
    big = 2**62
    rows = [(big, 0, 0), (big, 0, 0), (-big, 0, 0), (-big, 0, 0)]
    assert reference(plan, rows) == canonical([(0,)])
    shards = [{"r": arrow(rows[:2])}, {"r": arrow(rows[2:])}]
    with pytest.raises(polars_engine.IntegerOverflow):
        run_sharded(plan, shards, sharded=["r"])
    # Interleaved, every partial sum fits.
    shards = [{"r": arrow(rows[::2])}, {"r": arrow(rows[1::2])}]
    got = run_sharded(plan, shards, sharded=["r"])
    assert got.to_pylist() == [{"s": 0}]


def int_avg(expr) -> str:
    """The Ibis expression's plan with every `avg` made Substrait's `avg` of
    `i64` with an `i64` result (`AggFn.iavg`): the exact mean, truncated
    toward zero. (The SQL lift writes `AVG` as a `SUM` and a `COUNT` divided
    as doubles.)"""
    p = json.loads(to_substrait_json(expr))
    names = {e["extensionFunction"]["functionAnchor"]: e["extensionFunction"]["name"]
             for e in p["extensions"]}  # fmt: skip

    def walk(node: object) -> None:
        if isinstance(node, dict):
            m = node.get("measure")
            if isinstance(m, dict) and names.get(m["functionReference"]) == "avg":
                m["outputType"] = {"i64": {"nullability": "NULLABILITY_NULLABLE"}}
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(p)
    return json.dumps(p)


def measures(plan: dict) -> set[str]:
    """The names of the aggregate functions a plan's measures call."""
    names = {e["extensionFunction"]["functionAnchor"]: e["extensionFunction"]["name"]
             for e in plan["extensions"]}  # fmt: skip
    found: set[str] = set()

    def walk(node: object) -> None:
        if isinstance(node, dict):
            if isinstance(node.get("measure"), dict):
                found.add(names[node["measure"]["functionReference"]])
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    return found


r_table = ibis.table(R, name="r")
s_table = ibis.table(S, name="s")
_j = r_table.join(s_table, "b")
_f = r_table.filter(r_table.a > -2)

#: Integer `AVG`s, split into a `SUM` and a `COUNT` per shard (#245).
INT_AVG = {
    "grouped": r_table.group_by("b").aggregate(m=r_table.a.mean()),
    "global": r_table.aggregate(m=r_table.c.mean(), n=r_table.count(), hi=r_table.a.max()),
    "mixed": _f.group_by("b").aggregate(m=_f.c.mean(), s=_f.a.sum(), m2=_f.a.mean()).order_by("b"),
    "filtered": r_table.group_by("b").aggregate(m=r_table.a.mean(where=r_table.c > 0)),
    "joined": _j.group_by("d").aggregate(m=_j.a.mean()),
}


@pytest.mark.parametrize("name", INT_AVG)
@SETTINGS
@given(data=rows_and_shards)
def test_integer_avg_splits_into_sum_and_count(name: str, data):
    rows, where = data
    plan = int_avg(INT_AVG[name])
    s = split(plan, ["r"])
    assert (s.mode, s.proved) == ("two_phase", True)
    assert measures(s.partial) <= {"sum", "count", "min", "max"}
    pairs = list(zip(rows, where, strict=True))
    shards = [{"r": arrow([row for row, k in pairs if k == i])} for i in range(4)]
    s_rows = pa.table({"b": [b for b, _ in S_ROWS], "d": [d for _, d in S_ROWS]})
    got = run_sharded(plan, shards, sharded=["r"], broadcast={"s": s_rows})
    assert canonical(tuple(r.values()) for r in got.to_pylist()) == reference(plan, rows)


def test_integer_avg_truncates_the_whole_mean():
    """The mean of -7, -8 and 5 is -3, truncated toward zero. The shards' own
    means, -7 and -1, would average to -4."""
    plan = int_avg(r_table.aggregate(m=r_table.a.mean()))
    rows = [(-7, 0, 0), (-8, 0, 0), (5, 0, None)]
    shards = [{"r": arrow(rows[:1])}, {"r": arrow(rows[1:])}, {"r": arrow([])}]
    got = run_sharded(plan, shards, sharded=["r"])
    assert got.to_pylist() == [{"m": -3}]
    assert reference(plan, rows) == canonical([(-3,)])
    # A group without values is NULL, also when some shards have it.
    plan = int_avg(r_table.group_by("b").aggregate(m=r_table.c.mean()))
    rows = [(1, 0, None), (2, 0, None), (3, 1, 4)]
    shards = [{"r": arrow(rows[:1])}, {"r": arrow(rows[1:])}]
    got = run_sharded(plan, shards, sharded=["r"])
    assert canonical(tuple(r.values()) for r in got.to_pylist()) == canonical([(0, None), (1, 4)])


# -- Split double sums within a proved bound (#428) --------------------------

F = ibis.schema({"g": "int64", "x": "float64"})


def float_plan(sql: str) -> str:
    con = connect()
    con.create("f", F)
    return substrait_json(con, sql, semantics="duckdb")


def f_arrow(rows: list[tuple]) -> pa.Table:
    return pa.table(
        {
            "g": pa.array([g for g, _ in rows], pa.int64()),
            "x": pa.array([x for _, x in rows], pa.float64()),
        }
    )


def f_shards(rows: list[tuple], where: list[int]) -> list[dict[str, pa.Table]]:
    pairs = list(zip(rows, where, strict=True))
    return [{"f": f_arrow([r for r, k in pairs if k == i])} for i in range(4)]


def lean_sum(xs: list[float]) -> float | None:
    """`floatSum`: the values added in one pass, in order, from `0.0`."""
    if not xs:
        return None
    s = 0.0
    for x in xs:
        s += x
    return s


def lean_groups(rows: list[tuple]) -> dict[int | None, list[float]]:
    out: dict[int | None, list[float]] = {}
    for g, x in rows:
        out.setdefault(g, [])
        if x is not None:
            out[g].append(x)
    return out


#: Doubles that cancel, and that span every magnitude a double has.
ADVERSARIAL = [
    1e16,
    -1e16,
    1.0,
    -1.0,
    3.0,
    0.1,
    1e-300,
    -1e-300,
    1e300,
    -1e300,
    2.0**53,
    -(2.0**53),
]
doubles = st.one_of(
    st.sampled_from(ADVERSARIAL),
    st.floats(-1e300, 1e300, allow_nan=False, allow_infinity=False),
    st.builds(lambda m, e: m * 10.0**e, st.floats(-10, 10), st.integers(-300, 299)),
    st.none(),
)
#: The bound is cheap to check, so the double tests try more splits.
FLOAT_SETTINGS = settings(SETTINGS, max_examples=100)
f_rows_and_shards = st.lists(st.tuples(st.integers(0, 2), doubles), max_size=16).flatmap(
    lambda rows: st.tuples(
        st.just(rows), st.lists(st.integers(0, 3), min_size=len(rows), max_size=len(rows))
    )
)


def test_tolerance_matches_lean():
    """`shard_tol_scaled` and `shard_avg_tol_scaled` are `FloatCode`'s
    (the `#guard`s in `SubstraitLean/Partition.lean`)."""
    from sverify.partition import shard_avg_tol_scaled, shard_tol_scaled

    assert shard_tol_scaled(0, 0, 0, 0) == 0
    assert str(shard_tol_scaled(1, 1, 1, 2**1074)).startswith(
        "6741349255733686649825204000179208364406"
    )
    assert str(shard_tol_scaled(1000, 300, 4, 3 * 2**1080)).startswith(
        "5626060434865814519377634568766342"
    )
    assert str(shard_avg_tol_scaled(1, 1, 1, 2**1074)).startswith(
        "1572981493004527217599265855828681376492"
    )
    # About (γ 2 + γ 1) · (1 + 2 tiny) for one value of 1.0 in one shard.
    assert shard_tol_scaled(1, 1, 1, 2**1074) / 2**1074 == pytest.approx(3 * 2.0**-53, rel=1e-6)


def test_split_reports_where_the_bound_is():
    plan = float_plan("SELECT g, SUM(x) AS s, AVG(x) AS m, COUNT(*) AS n FROM f GROUP BY g")
    s = split(plan, ["f"], float_order="any")
    assert not s.proved
    fb = s.float_bounds
    assert fb is not None and fb["keys"] == 1
    assert [m["kind"] for m in fb["measures"]] == ["sum", "avg"]
    assert fb["columns"] == [{"key": 0}, {"bounded": 0}, {"bounded": 1}, {"exact": True}]
    assert s.bounded == {1: 0, 2: 1}
    assert not fb["filters_read_doubles"]
    # The partial rows hold `SUM(|x|)` (written as `abs`), `COUNT(x)` and `MAX(|x|)`.
    assert {"sum", "count", "max"} <= measures(s.partial)
    assert "abs" in functions(s.partial)
    # An exact split reports none.
    assert (
        split(float_plan("SELECT g, COUNT(*) AS n FROM f GROUP BY g"), ["f"]).float_bounds is None
    )


def functions(plan: dict) -> set[str]:
    """The names of every function a plan declares."""
    return {e["extensionFunction"]["name"] for e in plan["extensions"]}


@pytest.mark.parametrize(
    "sql",
    [
        "SELECT g, SUM(x) AS s, AVG(x) AS m FROM f GROUP BY g",
        "SELECT SUM(x) AS s, AVG(x) AS m, COUNT(x) AS n FROM f",
        "SELECT AVG(x) AS m, g FROM f WHERE g > 0 GROUP BY g",
    ],
)
@FLOAT_SETTINGS
@given(data=f_rows_and_shards)
def test_sharded_doubles_within_the_reported_tolerance(sql: str, data):
    """Cancelling values and values from 1e-300 to 1e300, split at random:
    each sharded `SUM`/`AVG` is within its reported τ of Lean's one-pass
    value, and τ is finite."""
    rows, where = data
    plan = float_plan(sql)
    shards = [
        {"f": f_arrow([r for r, k in zip(rows, where, strict=True) if k == i])} for i in range(4)
    ]
    got = run_sharded(plan, shards, sharded=["f"], reproducible=PLAN, tolerance=True)
    assert got.rows_exact
    grouped = "GROUP BY" in sql
    kept = [r for r in rows if "WHERE" not in sql or r[0] > 0]
    groups = lean_groups(kept) if grouped else {None: [x for _, x in kept if x is not None]}
    table = got.table.to_pylist()
    assert len(table) == len(groups)
    for i, row in enumerate(table):
        xs = groups[row["g"]] if grouped else groups[None]
        s = lean_sum(xs)
        for name, want in (("s", s), ("m", None if s is None else s / len(xs))):
            if name not in row:
                continue
            tau = got.tolerance[name][i]
            assert math.isfinite(tau)
            if want is None:
                assert row[name] is None
            else:
                assert abs(row[name] - want) <= tau, (name, row[name], want, tau)


@FLOAT_SETTINGS
@given(data=f_rows_and_shards)
def test_apriori_tolerance_bounds_the_split(data):
    """From a cap on the rows and a bound on `|x|`, before running."""
    rows, where = data
    xs = [x for _, x in rows if x is not None]
    assume(xs)
    plan = float_plan("SELECT SUM(x) AS s, AVG(x) AS m FROM f")
    shards = [
        {"f": f_arrow([r for r, k in zip(rows, where, strict=True) if k == i])} for i in range(4)
    ]
    got = run_sharded(plan, shards, sharded=["f"], reproducible=PLAN).to_pylist()[0]
    bound = max(abs(x) for x in xs)
    s = lean_sum(xs)
    assert s is not None
    assert abs(got["s"] - s) <= apriori_tolerance("sum", len(rows), bound, 4)
    assert abs(got["m"] - s / len(xs)) <= apriori_tolerance("avg", len(rows), bound, 4)


def test_cancellation_is_within_the_tolerance():
    """`1e16 + 1 − 1e16` is `0` in one pass and `1` split in two; the bound
    scales with `Σ|x|`, so it covers both."""
    plan = float_plan("SELECT SUM(x) AS s FROM f")
    shards = [{"f": f_arrow([(0, 1e16), (0, -1e16)])}, {"f": f_arrow([(0, 1.0)])}]
    got = run_sharded(plan, shards, sharded=["f"], reproducible=PLAN, tolerance=True)
    assert got.table.to_pylist() == [{"s": 1.0}]
    assert lean_sum([1e16, 1.0, -1e16]) == 0.0
    assert 1.0 <= got.tolerance["s"][0] < 20.0


def test_no_bound_where_it_does_not_carry_over():
    """An expression of a split double has no bound, a `HAVING` on one may
    keep other rows, and a group with NaN or near overflow has none."""
    plan = float_plan("SELECT g, SUM(x) * 2 AS s2 FROM f GROUP BY g HAVING SUM(x) > 1")
    shards = [{"f": f_arrow([(0, 1.5), (1, 3.0)])}, {"f": f_arrow([(0, 1.0)])}]
    got = run_sharded(plan, shards, sharded=["f"], reproducible=PLAN, tolerance=True)
    assert not got.rows_exact
    assert got.tolerance["s2"] == [math.inf, math.inf]
    plan = float_plan("SELECT g, SUM(x) AS s FROM f GROUP BY g")
    # Near overflow, short of it: `1e308 + 1e308` would raise (#575).
    shards = [{"f": f_arrow([(0, math.nan), (1, 1e308), (2, 1.0)])}, {"f": f_arrow([(1, 7e307)])}]
    got = run_sharded(plan, shards, sharded=["f"], reproducible=PLAN, tolerance=True)
    tau = {r["g"]: t for r, t in zip(got.table.to_pylist(), got.tolerance["s"], strict=True)}
    assert tau[0] == math.inf and tau[1] == math.inf and math.isfinite(tau[2])


def test_tolerance_without_the_keys_in_the_output():
    """Without the grouping keys, each row gets the largest τ of any group."""
    plan = float_plan("SELECT SUM(x) AS s FROM f GROUP BY g")
    shards = [{"f": f_arrow([(0, 1.0), (1, 1e10)])}, {"f": f_arrow([(1, 1.0)])}]
    got = run_sharded(plan, shards, sharded=["f"], reproducible=PLAN, tolerance=True)
    big = run_sharded(
        float_plan("SELECT g, SUM(x) AS s FROM f GROUP BY g"),
        shards,
        sharded=["f"],
        reproducible=PLAN,
        tolerance=True,
    )
    assert got.tolerance["s"] == [max(big.tolerance["s"])] * 2


def test_a_stated_tolerance_is_checked_against_the_bound():
    """`reproducible=sv.equivalent(floats=sv.within(...))` splits the
    doubles and raises where a row's τ exceeds the tolerance."""
    plan = float_plan("SELECT SUM(x) AS s FROM f")
    shards = [{"f": f_arrow([(0, 1e16), (0, -1e16)])}, {"f": f_arrow([(0, 1.0)])}]
    loose = sv.equivalent(floats=sv.within(abs=100.0))
    assert run_sharded(plan, shards, sharded=["f"], reproducible=loose).to_pylist() == [{"s": 1.0}]
    tight = sv.equivalent(floats=sv.within(abs=1e-3))
    with pytest.raises(ValueError, match="does not cover"):
        run_sharded(plan, shards, sharded=["f"], reproducible=tight)
    # Exact doubles refuse the split, as without `reproducible`.
    with pytest.raises(NotShardable):
        run_sharded(plan, shards, sharded=["f"], reproducible=sv.equivalent())


def test_float_order_is_deprecated():
    plan = float_plan("SELECT SUM(x) AS s FROM f")
    shards = [{"f": f_arrow([(0, 1.0)])}, {"f": f_arrow([(0, 2.0)])}]
    with pytest.warns(DeprecationWarning, match="float_order"):
        got = run_sharded(plan, shards, sharded=["f"], float_order="any")
    assert got.to_pylist() == [{"s": 3.0}]
    with pytest.raises(TypeError, match="not both"):
        run_sharded(plan, shards, sharded=["f"], float_order="any", reproducible=PLAN)

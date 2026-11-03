"""Aggregation: `GROUP BY` with `COUNT`, `SUM`, `MIN`, `MAX`, `AVG`.

* Lean's semantics (`aggregateEval`) agrees with DuckDB on random tables,
  including NULLs, empty tables (a global aggregate still gives one row),
  `DISTINCT` and `FILTER (WHERE …)` measures, and `HAVING`.
* Polars and DuckDB, which run the plan Lean writes, give Lean's rows, with
  doubles added in Lean's list order, so the same bits.
* Integer `SUM` may overflow, so it comes with a warning; the engines
  running the plan raise instead.
* The grouping columns are a key of the result, and contracts see through
  `COUNT`, `MIN`/`MAX` and the sign of a `SUM`.
"""

import json
import math

import duckdb
import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify import polars_engine
from sverify.contracts import decode_double
from sverify.engine import (
    collect,
    connect,
    create_table,
    run_plan,
    substrait_json,
    written_plan,
)
from sverify.ibis_substrait import to_substrait_json
from sverify.incremental import arrow_rows
from sverify.testing import canonical, duckdb_sql, inline_tables, lean_values
from sverify_dev.examples import orders

T = ibis.schema({"a": "int64", "b": "int64", "s": "string"})
F = ibis.schema({"k": "int64", "x": "float64"})

small = st.one_of(st.none(), st.integers(-2, 3))
t_rows = st.lists(st.tuples(small, small, st.sampled_from(["x", "y", "é", None])), max_size=7)
doubles = st.one_of(
    st.none(),
    st.sampled_from([0.5, 1.0, 2.25, -3.0, math.inf, -math.inf, math.nan]),
)
f_rows = st.lists(st.tuples(st.one_of(st.none(), st.integers(0, 2)), doubles), max_size=7)

EXACT = [
    "SELECT a, COUNT(*), SUM(b), MIN(b), MAX(b) FROM t GROUP BY a",
    "SELECT COUNT(*), COUNT(b), SUM(b), MIN(a), MAX(s) FROM t",
    "SELECT a, COUNT(DISTINCT b), SUM(DISTINCT b) FROM t GROUP BY a",
    "SELECT a, SUM(b) FILTER (WHERE b > 0), COUNT(*) FILTER (WHERE s = 'x') FROM t GROUP BY a",
    "SELECT a, COUNT(*) AS n FROM t GROUP BY a HAVING COUNT(*) > 1",
    "SELECT a + b, COUNT(*) FROM t GROUP BY a + b",
    "SELECT s, a, MIN(b) FROM t GROUP BY s, a",
    "SELECT s, MIN(s), MAX(s), COUNT(DISTINCT a) FROM t GROUP BY s",
    "SELECT a, MAX(b > 0), MIN(b > 0) FROM t GROUP BY a",
    "SELECT DISTINCT a + 1 FROM t",
]


def duckdb_rows_of(sql: str, schema: ibis.Schema, rows: list) -> list[tuple]:
    """DuckDB running `sql`, the oracle for the lifted plan."""
    con = connect()
    create_table(con, "t", schema, rows)
    out = duckdb_sql(con, sql)
    return list(zip(*(c.to_pylist() for c in out.columns), strict=True))


def datafusion_rows(sql: str, schema: ibis.Schema, rows: list) -> list[tuple]:
    """DataFusion running `sql`, as an engine."""
    con = connect()
    create_table(con, "t", schema, rows)
    out = collect(con._datafusion_session.sql(sql))
    return list(zip(*(c.to_pylist() for c in out.columns), strict=True))


def run(sql: str, schema: ibis.Schema, rows: list) -> tuple[list[tuple], list[tuple]]:
    expected = duckdb_rows_of(sql, schema, rows)
    con = connect()
    create_table(con, "t", schema, rows)
    plan = inline_tables(json.loads(substrait_json(con, sql)), {"t": rows})
    return lean_values(json.dumps(plan)), expected


@pytest.mark.parametrize("sql", EXACT)
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(t=t_rows)
def test_aggregates_match_duckdb(sql, t):
    got, expected = run(sql, T, t)
    assert canonical(got) == canonical(expected)


def engine_rows(sql: str, schema: ibis.Schema, rows: list, *engines: str) -> dict[str, list[tuple]]:
    con = connect()
    create_table(con, "t", schema, rows)
    plan = written_plan(substrait_json(con, sql))
    return {
        e: [tuple(r.values()) for r in run_plan(con, plan, e).to_pylist()]
        for e in engines or ("polars", "duckdb")
    }


@pytest.mark.parametrize("sql", EXACT)
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(t=t_rows)
def test_engines_match_duckdb(sql, t):
    out = engine_rows(sql, T, t)
    assert canonical(out["polars"]) == canonical(out["duckdb"])
    assert canonical(out["polars"]) == canonical(duckdb_rows_of(sql, T, t))


def test_engines_raise_where_sum_wraps():
    rows = [(1, 2**62, "x"), (1, 2**62, "y")]
    sql = "SELECT a, SUM(b) FROM t GROUP BY a"
    with pytest.raises(polars_engine.IntegerOverflow):
        engine_rows(sql, T, rows)
    con = connect()
    create_table(con, "t", T, rows)
    with pytest.raises(duckdb.Error, match="overflow in SUM"):
        run_plan(con, written_plan(substrait_json(con, sql)), "duckdb")


def close(x: object, y: object) -> bool:
    """Lean prints doubles with six decimals."""
    if isinstance(x, float) and isinstance(y, float):
        if math.isnan(x) or math.isnan(y):
            return math.isnan(x) and math.isnan(y)
        return x == y or math.isclose(x, y, rel_tol=1e-6, abs_tol=1e-6)
    return x == y


FLOATS = [
    "SELECT k, SUM(x), AVG(x), COUNT(x) FROM t GROUP BY k",
    "SELECT x, COUNT(*) FROM t GROUP BY x",
    "SELECT k, AVG(k) FROM t GROUP BY k",
    "SELECT AVG(x), SUM(x) FROM t",
]


@pytest.mark.parametrize("sql", FLOATS)
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(t=f_rows)
def test_double_aggregates_match_duckdb(sql, t):
    got, expected = run(sql, F, t)
    # Lean prints tiny doubles (±0.0) as their codes.
    floats = {i for row in expected for i, v in enumerate(row) if isinstance(v, float)}
    got = [
        tuple(
            decode_double(v) if i in floats and isinstance(v, int) else v for i, v in enumerate(row)
        )
        for row in got
    ]
    # Group keys are exact: sort both by them (rendered), then compare loosely.
    got, expected = sorted(got, key=repr), sorted(expected, key=repr)
    assert len(got) == len(expected)
    for g, e in zip(got, expected, strict=True):
        assert all(close(x, y) for x, y in zip(g, e, strict=True)), (g, e)


@pytest.mark.parametrize("sql", FLOATS)
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(t=f_rows)
def test_engines_add_doubles_in_lean_order(sql, t):
    """Both engines add in Lean's list order, so they agree bit for bit; with
    DuckDB running the SQL, whose order is its own, only approximately. A double sum of
    `+inf` and `-inf` would be NaN, so both raise there (#257)."""
    if both_infinities(sql, t):
        for engine in ("duckdb", "polars"):
            with pytest.raises(Exception, match="(?i)domain|NaN"):
                engine_rows(sql, F, t, engine)
        return
    out = engine_rows(sql, F, t)
    assert canonical(out["polars"]) == canonical(out["duckdb"])  # bit for bit
    expected = sorted(duckdb_rows_of(sql, F, t), key=repr)
    got = sorted(out["polars"], key=repr)
    assert len(got) == len(expected)
    for g, e in zip(got, expected, strict=True):
        assert all(close(x, y) for x, y in zip(g, e, strict=True)), (g, e)


def both_infinities(sql: str, rows: list) -> bool:
    """Does a `SUM(x)` or `AVG(x)` of `sql` see `+inf` and `-inf` in one group?"""
    if "SUM(x)" not in sql and "AVG(x)" not in sql:
        return False
    groups: dict = {}
    for k, x in rows:
        groups.setdefault(k if "GROUP BY k" in sql else None, set()).add(x)
    return any(math.inf in g and -math.inf in g for g in groups.values())


EXTREMES = "SELECT k, MIN(x), MAX(x), COUNT(x) FROM t GROUP BY k"


@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(t=f_rows)
def test_min_and_max_of_doubles_match_duckdb(t):
    # DuckDB orders doubles as the model does, -∞ < … < +∞ < NaN (#371).
    got, expected = run(EXTREMES, F, t)
    lean = engine_rows(EXTREMES, F, t, "duckdb")["duckdb"]
    assert canonical(lean) == canonical(expected)
    floats = {1, 2}
    got = [
        tuple(
            decode_double(v) if i in floats and isinstance(v, int) else v for i, v in enumerate(r)
        )
        for r in got
    ]
    got, expected = sorted(got, key=repr), sorted(expected, key=repr)
    for g, e in zip(got, expected, strict=True):
        assert all(close(x, y) for x, y in zip(g, e, strict=True)), (g, e)


def test_avg_of_doubles_rounds_past_the_values():
    # IEEE's mean of three 0.1 is 0.10000000000000002, above every value, so
    # the reference claims no bound on an `AVG` of doubles (#85 bounds it).
    rows = [(1, 0.1), (1, 0.1), (1, 0.1)]
    sql = "SELECT k, AVG(x) FROM t GROUP BY k"
    mean = (0.1 + 0.1 + 0.1) / 3
    assert mean > 0.1
    assert engine_rows(sql, F, rows) == {"polars": [(1, mean)], "duckdb": [(1, mean)]}


@pytest.mark.backend("datafusion")
def test_min_and_max_of_doubles_are_refused_on_datafusion():
    # DataFusion's grouped MIN of a group of +∞ is the largest finite double.
    expected = datafusion_rows("SELECT k, MIN(x) FROM t GROUP BY k", F, [(1, math.inf)])
    assert expected == [(1, 1.7976931348623157e308)]
    with pytest.raises(ValueError, match="MIN and MAX of doubles are not yet supported"):
        engine_rows("SELECT k, MIN(x) FROM t GROUP BY k", F, [(1, math.inf)], "datafusion")


def test_min_and_max_of_doubles_are_refused_on_polars():
    with pytest.raises(Exception, match="(?i)not yet supported on Polars|unsupported aggregate"):
        engine_rows(EXTREMES, F, [(1, 0.5)], "polars")


samples = ibis.table({"host": "!string", "cpu": "!float64"}, name="samples")


def test_min_and_max_of_doubles_are_proved():
    # #371: `MIN` and `MAX` of doubles are among the values.
    report = sv.verify(
        samples.group_by("host").aggregate(lo=samples.cpu.min(), hi=samples.cpu.max()),
        requires={"samples": [_.cpu >= 0, _.cpu <= 100]},
        ensures=[_.hi <= 100, _.lo >= 0, _.lo <= _.hi, _.hi.notnull()],
    )
    assert report.proved, str(report)


def test_rollup_contract_is_proved():
    # #372: a per-minute rollup's contract, from the issue.
    s = ibis.table({"host": "!string", "ts": "!timestamp(6)", "cpu": "!int32"}, name="s")
    m = s.mutate(minute=s.ts.truncate("m"))
    g = m.group_by(["host", "minute"]).aggregate(
        n=m.count(), avg=m.cpu.mean(), lo=m.cpu.min(), mx=m.cpu.max()
    )
    report = sv.verify(
        g,
        requires={"s": [_.cpu >= 0, _.cpu <= 1000]},
        ensures=[_.mx.notnull(), _.mx <= 1000, _.lo <= _.mx, _.avg.notnull()],
    )
    assert report.proved, str(report)
    assert report.facts["mx"] == "an integer in [0, 1000]"
    # The mean is a double division, which rounds: no bound from the inputs (#85).
    report = sv.verify(
        g, requires={"s": [_.cpu >= 0, _.cpu <= 1000]}, ensures=[_.mx >= _.avg, _.avg <= 1000]
    )
    assert [c.proved for c in report.ensures] == [False, False]


def test_avg_of_doubles_is_not_null_but_unbounded():
    g = samples.group_by("host").aggregate(avg=samples.cpu.mean(), hi=samples.cpu.max())
    report = sv.verify(
        g,
        requires={"samples": [_.cpu >= 0, _.cpu <= 100]},
        ensures=[_.avg.notnull(), _.avg <= 100, _.avg <= _.hi],
    )
    assert [c.proved for c in report.ensures] == [True, False, False]


def test_decimal_avg_is_bounded_by_its_inputs():
    # #237: a decimal `AVG` is its exact `SUM` by its `COUNT`, rounded.
    t = ibis.table({"k": "!int64", "q": "!decimal(12, 2)"}, name="lineitem")
    g = t.group_by("k").aggregate(avg_q=t.q.mean())
    report = sv.verify(
        g, requires={"lineitem": [_.q >= 1, _.q <= 50]}, ensures=[_.avg_q >= 1, _.avg_q <= 50]
    )
    assert report.proved, str(report)


def test_avg_of_a_nullable_column_may_be_null():
    t = ibis.table({"k": "!int64", "x": "float64"}, name="readings")
    g = t.group_by("k").aggregate(avg=t.x.mean(), hi=t.x.max())
    # A group may have only NULLs.
    report = sv.verify(g, ensures=[_.avg.notnull(), _.hi.notnull()])
    assert [c.proved for c in report.ensures] == [False, False]


def test_integer_sum_overflow_is_a_warning():
    # Lean's sum is exact, so the checker warns of an overflow at run time
    # (DataFusion's wrap-around is pinned in test_datafusion_quirks.py).
    report = sv.verify(orders.aggregate(total=orders.amount.sum()))
    assert [str(i) for i in report.issues] == ["SUM overflow: $2"]
    assert report.proved  # checked while the job runs, not against the proof (#202)


by_customer = orders.group_by("customer").aggregate(
    n=orders.count(), total=orders.amount.sum(), top=orders.amount.max()
)


def test_aggregate_postconditions_are_proved():
    report = sv.verify(
        by_customer,
        requires={"orders": [_.amount >= 0]},
        ensures=[
            # Every group has a row (#229).
            _.n >= 1,
            _.n.notnull(),
            _.total.isnull() | (_.total >= 0),
            _.top.isnull() | (_.top >= 0),
            sv.unique("customer"),
        ],
    )
    assert report.proved, str(report)
    assert report.facts["n"] == "an integer ≥ 1"
    # `amount >= 0` rules out NULL, so each group has a maximum (#372).
    assert report.facts["top"] == "an integer ≥ 0"


def test_sum_has_no_upper_bound():
    report = sv.verify(
        by_customer,
        requires={"orders": [_.amount <= 10]},
        ensures=[_.top.isnull() | (_.top <= 10), _.total.isnull() | (_.total <= 10)],
    )
    assert [c.proved for c in report.ensures] == [True, False]


def test_a_global_aggregate_has_one_row():
    report = sv.verify(orders.aggregate(n=orders.count()), ensures=[sv.unique()])
    assert report.proved, str(report)


def test_errors_in_measures_are_reported():
    expr = orders.group_by("customer").aggregate(q=(100 // orders.amount).sum())
    report = sv.verify(expr)
    assert any(i.kind == "division by zero" for i in report.errors)
    guarded = (
        orders.filter(orders.amount != 0)
        .group_by("customer")
        .aggregate(q=(100 // orders.amount).max())
    )
    assert not sv.verify(guarded).errors


B = ibis.table({"a": "int64", "b": "int64"}, name="t")
i64 = st.integers(-(2**63), 2**63 - 1)


def bit_fold(op, vs: list) -> int | None:
    """`AggFn.bit`: the operation over the non-NULL values, NULL without one."""
    vs = [v for v in vs if v is not None]
    if not vs:
        return None
    acc = -1 if op == "and" else 0
    for v in vs:
        acc = acc & v if op == "and" else acc | v if op == "or" else acc ^ v
    return acc


@settings(
    max_examples=30, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(t=st.lists(st.tuples(small, st.one_of(st.none(), i64)), max_size=7))
def test_bit_aggregates_match_every_engine(t):
    """`AggFn.bit` (#53): the 64-bit operation folded over the non-NULL values."""
    expr = B.group_by("a").aggregate(
        x=B.b.bit_and(), o=B.b.bit_or(), r=B.b.bit_xor(), p=B.b.bit_xor(where=B.b > 0)
    )
    groups: dict = {}
    for a, b in t:
        groups.setdefault(a, []).append(b)
    expected = sorted(
        (
            (a, bit_fold("and", vs), bit_fold("or", vs), bit_fold("xor", vs),
             bit_fold("xor", [v for v in vs if v is not None and v > 0]))
            for a, vs in groups.items()
        ),
        key=repr,
    )  # fmt: skip
    plan = to_substrait_json(expr)
    lean = lean_values(json.dumps(inline_tables(json.loads(plan), {"t": t})))
    assert sorted(lean, key=repr) == expected
    con = connect()
    create_table(con, "t", B.schema(), t)
    written = written_plan(plan)
    for engine in ("duckdb", "polars", "datafusion"):
        got = [tuple(r.values()) for r in run_plan(con, written, engine).to_pylist()]
        assert sorted(got, key=repr) == expected, engine


# #54: variance and standard deviation with each engine's own algorithm,
# compared approximately (#85 will bound the error).
V = ibis.table({"k": "int64", "x": "float64", "i": "int64"}, name="t")
finite = st.one_of(
    st.none(),
    st.sampled_from([0.0, 0.1, -2.5, 1e150, -1e-300, math.nan]),
    st.floats(-1e6, 1e6, allow_nan=False),
)
v_rows = st.lists(
    st.tuples(st.integers(0, 2), finite, st.one_of(st.none(), st.integers(-(10**6), 10**6))),
    max_size=8,
)


def var_expr():
    return V.group_by("k").aggregate(
        vs=V.x.var(), vp=V.x.var(how="pop"), ss=V.x.std(), sp=V.x.std(how="pop"), vi=V.i.var()
    )


def decoded(rows: list[tuple]) -> list[tuple]:
    """Lean writes doubles as codes; NaN as text so it equals itself."""
    out = []
    for r in rows:
        vals = [r[0], *(None if v is None else decode_double(v) if isinstance(v, int) else v
                        for v in r[1:])]  # fmt: skip
        out.append(tuple("nan" if isinstance(v, float) and v != v else v for v in vals))
    return sorted(out, key=repr)


def near(x: object, y: object) -> bool:
    """Equal up to the algorithm's rounding (and Lean's six printed decimals)."""
    if isinstance(x, float) and isinstance(y, float):
        return math.isclose(x, y, rel_tol=1e-6, abs_tol=1e-6)
    return x == y


@settings(max_examples=40, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(rows=v_rows)
def test_variance_agrees_across_engines(rows):
    con = connect()
    create_table(con, "t", V.schema(), rows)
    plan = to_substrait_json(var_expr())
    lean = decoded(lean_values(json.dumps(inline_tables(json.loads(plan), {"t": rows}))))
    written = written_plan(plan)
    for engine in ("duckdb", "polars", "datafusion"):
        got = decoded(arrow_rows(run_plan(con, written, engine)))
        assert len(got) == len(lean), engine
        for g, e in zip(got, lean, strict=True):
            assert all(near(x, y) for x, y in zip(g, e, strict=True)), (engine, g, e)
            # Only the sign is claimed exactly: never negative.
            assert all(not isinstance(x, float) or x != x or x >= 0 for x in g[1:]), g


def test_variance_meaning():
    """A sample of one value is NULL; a population of one is 0."""
    con = connect()
    rows = [(1, 1.5, 1), (1, 2.25, 2), (1, -3.0, 3), (2, 7.0, 4), (2, None, None)]
    create_table(con, "t", V.schema(), rows)
    mean = (1.5 + 2.25 - 3.0) / 3
    ss = sum((x - mean) * (x - mean) for x in (1.5, 2.25, -3.0))
    expected = [
        (1, ss / 2, ss / 3, math.sqrt(ss / 2), math.sqrt(ss / 3), 1.0),
        (2, None, 0.0, None, 0.0, None),
    ]
    written = written_plan(to_substrait_json(var_expr()))
    for engine in ("duckdb", "polars", "datafusion"):
        got = decoded(arrow_rows(run_plan(con, written, engine)))
        for g, e in zip(got, expected, strict=True):
            assert all(near(x, y) for x, y in zip(g, e, strict=True)), (engine, g, e)
    report = sv.verify(var_expr())
    assert all(report.facts[c] == "a double ≥ 0.0 or NULL" for c in ("vs", "vp", "ss", "sp")), (
        report.facts
    )


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_variance_of_an_infinity_raises(engine):
    """`inf - mean` would be NaN, which no operation creates (#257)."""
    con = connect()
    create_table(con, "t", V.schema(), [(1, math.inf, 1), (1, 2.0, 2)])
    with pytest.raises(Exception, match="(?i)domain|NaN"):
        run_plan(con, written_plan(to_substrait_json(var_expr())), engine)
    report = sv.verify(var_expr())
    assert "domain error" in [i.kind for i in report.issues]
    bounded = sv.verify(var_expr(), requires={"t": [_.x < 1e300, _.x > -1e300]})
    assert "domain error" not in [i.kind for i in bounded.issues]


# #55: FIRST and LAST in a given order, NULLs skipped; ties in list order.
P = ibis.table({"k": "int64", "x": "string", "o": "int64"}, name="t")


def first_last(rows: list, last: bool, desc: bool) -> dict:
    """Python's reference: per group, the first (or last) non-NULL `x` after a
    stable sort by `o` (NULLs last, as Ibis orders)."""
    out: dict = {}
    for k in {r[0] for r in rows}:
        grp = [r for r in rows if r[0] == k and r[1] is not None]
        nulls = [r for r in grp if r[2] is None]
        vals = sorted((r for r in grp if r[2] is not None), key=lambda r: r[2], reverse=desc)
        # `sorted` is stable, but reverse=True keeps ties in order too.
        ordered = vals + nulls
        out[k] = (ordered[-1] if last else ordered[0])[1] if ordered else None
    return out


@settings(max_examples=40, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(
    rows=st.lists(
        st.tuples(
            st.integers(0, 2),
            st.one_of(st.none(), st.sampled_from(["a", "b", "c"])),
            st.one_of(st.none(), st.integers(0, 3)),
        ),
        max_size=8,
    )
)
def test_first_and_last_follow_their_order(rows):
    expr = P.group_by("k").aggregate(
        f=P.x.first(order_by=P.o), l=P.x.last(order_by=P.o), d=P.x.first(order_by=ibis.desc(P.o))
    )
    plan = to_substrait_json(expr)
    expected = sorted(
        (k, first_last(rows, False, False)[k], first_last(rows, True, False)[k],
         first_last(rows, False, True)[k])
        for k in {r[0] for r in rows}
    )  # fmt: skip
    lean = sorted(lean_values(json.dumps(inline_tables(json.loads(plan), {"t": rows}))))
    assert lean == expected
    con = connect()
    create_table(con, "t", P.schema(), rows)
    got = sorted(tuple(r.values()) for r in run_plan(con, written_plan(plan), "duckdb").to_pylist())
    assert got == expected


def test_first_and_last_are_determined_by_a_key():
    """Ties make the choice the engine's, unless the group and order columns
    contain a key (`Rel.windowsTotal`); other engines refuse it for now (#271)."""
    expr = P.group_by("k").aggregate(f=P.x.first(order_by=P.o))
    assert not sv.verify(expr).deterministic
    assert sv.verify(expr, requires={"t": [sv.unique("k", "o")]}).deterministic
    con = connect()
    create_table(con, "t", P.schema(), [(1, "a", 1)])
    written = written_plan(to_substrait_json(expr))
    for engine in ("polars", "datafusion"):
        with pytest.raises(Exception, match="see #271"):
            run_plan(con, written, engine)
    # Without an order every row ties: determined only by a key on the group.
    any_row = P.group_by("k").aggregate(f=P.x.first())
    assert not sv.verify(any_row, requires={"t": [sv.unique("k", "o")]}).deterministic
    assert sv.verify(any_row, requires={"t": [sv.unique("k")]}).deterministic


# #55: Ibis's distinct(on=) is FIRST/LAST of each other column without an
# order, each column on its own (DuckDB may take them from different rows).
D = ibis.table({"name": "string", "a": "int64", "b": "int64"}, name="t")


@pytest.mark.parametrize("keep", ["first", "last", None])
@settings(max_examples=30, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(
    rows=st.lists(
        st.tuples(
            st.sampled_from(["x", "y", None]),
            st.one_of(st.none(), st.integers(0, 3)),
            st.one_of(st.none(), st.integers(0, 3)),
        ),
        max_size=6,
    )
)
def test_distinct_on_runs_as_lean_says(keep, rows):
    """DuckDB's written plan breaks every tie in Lean's list order."""
    plan = to_substrait_json(D.distinct(on="name", keep=keep))
    lean = sorted(lean_values(json.dumps(inline_tables(json.loads(plan), {"t": rows}))), key=repr)
    con = connect()
    create_table(con, "t", D.schema(), rows)
    got = run_plan(con, written_plan(plan), "duckdb").to_pylist()
    assert sorted((tuple(r.values()) for r in got), key=repr) == lean


def test_distinct_on_proves_nothing_about_one_row():
    """Each kept column may come from a different row of its group, so `a <= b`,
    true on every row, is not proved; nor is anything else unless `name` is a
    key, which makes each group one row."""
    expr = D.distinct(on="name")
    rows_ok = [_.a <= _.b, _.a.notnull(), _.b.notnull()]
    report = sv.verify(expr, requires={"t": rows_ok}, ensures=[_.a <= _.b])
    assert not report.deterministic
    assert not report.proved
    # LAST of each column skips NULLs on its own: a and b from different rows.
    con = connect()
    create_table(con, "t", D.schema(), [("x", 1, 5), ("x", 3, None), ("x", None, 2)])
    got = run_plan(
        con, written_plan(to_substrait_json(D.distinct(on="name", keep="last"))), "duckdb"
    )
    assert [tuple(r.values()) for r in got.to_pylist()] == [("x", 3, 2)]
    keyed = sv.verify(expr, requires={"t": [*rows_ok, sv.unique("name")]}, ensures=[_.a <= _.b])
    assert keyed.deterministic


# #54: covariance and correlation of pairs of doubles, each engine's own
# algorithm; CORR is NULL where the SQL standard says (DuckDB gives NaN).
C = ibis.table({"k": "int64", "x": "float64", "y": "float64"}, name="t")


def cov_expr():
    return C.group_by("k").aggregate(cs=C.x.cov(C.y), cp=C.x.cov(C.y, how="pop"), r=C.x.corr(C.y))


@settings(max_examples=40, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(
    rows=st.lists(
        st.tuples(
            st.integers(0, 2),
            # Ordinary values: near the subnormals each engine's algorithm
            # rounds its own way (DuckDB's CORR then gives NaN).
            st.one_of(st.none(), st.integers(-1000, 1000).map(lambda i: i / 4)),
            st.one_of(st.none(), st.integers(-1000, 1000).map(lambda i: i / 8)),
        ),
        max_size=8,
    )
)
def test_covariance_agrees_with_duckdb(rows):
    plan = to_substrait_json(cov_expr())
    lean = sorted(lean_values(json.dumps(inline_tables(json.loads(plan), {"t": rows}))), key=repr)
    con = connect()
    create_table(con, "t", C.schema(), rows)
    got = sorted(
        (tuple(r.values()) for r in run_plan(con, written_plan(plan), "duckdb").to_pylist()),
        key=repr,
    )
    lean = sorted((tuple(decode_double(v) if isinstance(v, int) and i else v
                         for i, v in enumerate(r)) for r in lean), key=repr)  # fmt: skip
    assert len(got) == len(lean)
    for g, e in zip(got, lean, strict=True):
        assert all(near(a, b) for a, b in zip(g, e, strict=True)), (g, e)


def test_correlation_is_null_where_the_standard_says():
    """Fewer than two pairs, or a side whose values are all equal: NULL (DuckDB's
    own CORR gives NaN); other engines refuse it for now (#271)."""
    con = connect()
    rows = [
        (1, 1.0, 2.0),
        (1, 2.0, 4.0),
        (2, 1.0, 1.0),
        (2, 1.0, 2.0),
        (3, None, 1.0),
        (4, 1.0, 1.0),
    ]
    create_table(con, "t", C.schema(), rows)
    written = written_plan(to_substrait_json(cov_expr()))
    got = sorted(tuple(r.values()) for r in run_plan(con, written, "duckdb").to_pylist())
    assert got == [
        (1, 1.0, 0.5, 1.0),
        (2, 0.0, 0.0, None),
        (3, None, None, None),
        (4, None, 0.0, None),
    ]
    for engine in ("polars", "datafusion"):
        with pytest.raises(Exception, match="see #271"):
            run_plan(con, written, engine)


def test_covariance_of_an_infinity_raises():
    """`inf - mean` would be NaN, which no operation creates (#257): `verify`
    reports a domain error, bounds rule it out, and DuckDB raises."""
    report = sv.verify(cov_expr())
    assert "domain error" in [i.kind for i in report.issues]
    finite = [_.x < 1e300, _.x > -1e300, _.y < 1e300, _.y > -1e300]
    assert "domain error" not in [
        i.kind for i in sv.verify(cov_expr(), requires={"t": finite}).issues
    ]
    con = connect()
    create_table(con, "t", C.schema(), [(1, math.inf, 1.0), (1, 2.0, 3.0)])
    with pytest.raises(Exception, match="(?i)domain"):
        run_plan(con, written_plan(to_substrait_json(cov_expr())), "duckdb")


# #55: STRING_AGG (Ibis's group_concat) in a given order, NULLs skipped.
def joined(rows: list, sep: str, desc: bool) -> dict:
    """Python's reference: per group, the non-NULL `x` after a stable sort by
    `o` (NULLs last, as Ibis orders), joined by `sep`; None without values."""
    out: dict = {}
    for k in {r[0] for r in rows}:
        grp = [r for r in rows if r[0] == k and r[1] is not None]
        nulls = [r for r in grp if r[2] is None]
        vals = sorted((r for r in grp if r[2] is not None), key=lambda r: r[2], reverse=desc)
        out[k] = sep.join(r[1] for r in vals + nulls) if grp else None
    return out


@settings(max_examples=40, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(
    rows=st.lists(
        st.tuples(
            st.integers(0, 2),
            st.one_of(st.none(), st.sampled_from(["a", "b", "", "é"])),
            st.one_of(st.none(), st.integers(0, 3)),
        ),
        max_size=8,
    )
)
def test_group_concat_follows_its_order(rows):
    expr = P.group_by("k").aggregate(
        s=P.x.group_concat(",", order_by=P.o), d=P.x.group_concat("--", order_by=ibis.desc(P.o))
    )
    plan = to_substrait_json(expr)
    up, down = joined(rows, ",", False), joined(rows, "--", True)
    expected = sorted(((k, up[k], down[k]) for k in up), key=repr)
    lean = sorted(lean_values(json.dumps(inline_tables(json.loads(plan), {"t": rows}))), key=repr)
    assert lean == expected
    con = connect()
    create_table(con, "t", P.schema(), rows)
    got = run_plan(con, written_plan(plan), "duckdb").to_pylist()
    assert sorted((tuple(r.values()) for r in got), key=repr) == expected


def test_group_concat_is_determined_by_a_key():
    """Ties make the order the engine's, unless the group and order columns
    contain a key (`Rel.windowsTotal`); without `order_by` it is refused, and
    other engines refuse it for now (#271)."""
    expr = P.group_by("k").aggregate(s=P.x.group_concat(",", order_by=P.o))
    assert not sv.verify(expr).deterministic
    assert sv.verify(expr, requires={"t": [sv.unique("k", "o")]}).deterministic
    con = connect()
    create_table(con, "t", P.schema(), [(1, "a", 1)])
    written = written_plan(to_substrait_json(expr))
    for engine in ("polars", "datafusion"):
        with pytest.raises(Exception, match="see #271"):
            run_plan(con, written, engine)
    with pytest.raises(Exception, match="engine's order"):
        to_substrait_json(P.group_by("k").aggregate(s=P.x.group_concat(",")))

"""Contracts: postconditions are proved from preconditions, or refused."""

import warnings
from datetime import date, datetime

import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from _pipelines import bound_orders
from sverify.contracts import OVERFLOW_HINT, violations
from sverify.engines import create_table
from sverify.errors import PostconditionError, PreconditionError, VerificationError
from sverify_dev.examples import customers, orders


@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 2**62, _.id.notnull()]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL", _.doubled > 20],
)
def doubled(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


def test_postconditions_are_proved():
    doubled(orders)
    report = doubled.report
    assert report is not None
    assert report.proved
    assert report.facts["doubled"] == "an integer ≥ 22"
    assert "(_.amount < 4611686018427387904)" in report.requires["orders"]  # stated (#655)
    assert report.inferred == {}
    assert report.facts["id"] == "any integer"  # never NULL, by the precondition


def test_unprovable_postcondition_is_refused():
    @sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
    def plus_one(orders):
        return orders.select(orders.id, total=orders.amount + 1)

    with pytest.raises(VerificationError) as e:
        plus_one(orders)
    assert e.value.report.unproved[0].value == "TRUE or FALSE"
    assert e.value.report.facts["total"] == "an integer ≥ 1"


def test_null_propagates_unless_ruled_out():
    # Without a precondition, `amount + 1` can be NULL...
    report = sv.verify(orders.select(t=orders.amount + 1), ensures=[_.t.notnull()])
    assert not report.proved
    # ...and a filter on `amount` rules that out (NULL > 0 is not TRUE).
    report = sv.verify(
        orders.filter(orders.amount > 0).select(t=orders.amount + 1),
        requires={"orders": [_.amount < 1_000_000]},
        ensures=[_.t.notnull()],
    )
    assert report.proved


def test_equality_uses_intervals():
    zero = orders.select(t=orders.amount * 0)
    assert sv.verify(zero, requires={"orders": [_.amount.notnull()]}, ensures=[_.t == 0]).proved
    big = orders.filter(orders.amount > 10).select("amount")
    report = sv.verify(big, ensures=[_.amount != 5, _.amount == 5, _.amount == 11])
    assert [c.proved for c in report.ensures] == [True, False, False]
    assert report.ensures[1].value == "FALSE"  # 5 is outside [11, ∞)
    assert report.ensures[2].value == "TRUE or FALSE"


def test_inner_join_keeps_facts_left_join_does_not():
    inner = orders.join(customers, orders.customer == customers.name).select(
        orders.id, customers.city
    )
    left = orders.left_join(customers, orders.customer == customers.name).select(
        orders.id, customers.city
    )
    pre = {"customers": [_.city.notnull()]}
    assert sv.verify(inner, requires=pre, ensures=[_.city.notnull()]).proved
    report = sv.verify(left, requires=pre, ensures=[_.city.notnull()])
    assert not report.proved
    assert "NULL" in report.facts["city"]


def test_sql_transform_and_conditions():
    report = sv.verify(
        "select id, amount - 5 as rest from orders where amount >= 5",
        tables={"orders": orders},
        ensures=["rest >= 0", "rest IS NOT NULL"],
    )
    assert report.proved


def test_sql_transform_with_ibis_ensures():
    # #438: an Ibis condition binds to the lifted query's output schema.
    jobs = ibis.table({"workflow": "!string"}, name="jobs")
    report = sv.verify(
        "SELECT workflow, count(*) AS n FROM jobs GROUP BY workflow",
        tables={"jobs": jobs},
        ensures=[_.n >= 1, sv.unique("workflow")],
    )
    assert report.proved
    assert [c.label for c in report.ensures] == ["(_.n >= 1)", "unique(workflow)"]
    assert not sv.verify(
        "SELECT workflow, count(*) - 1 AS n FROM jobs GROUP BY workflow",
        tables={"jobs": jobs},
        ensures=[_.n >= 1],
        counterexamples=0,
    ).proved


def test_sql_transform_with_ibis_requires():
    # #438: an Ibis precondition binds to its input table's schema, beside SQL ones.
    report = sv.verify(
        "select id, amount - 5 as rest from orders",
        tables={"orders": orders, "customers": customers},
        requires={"orders": [_.amount >= 5, "amount <= 100"]},
        ensures=[_.rest >= 0, "rest <= 95"],
    )
    assert report.proved
    assert report.requires["orders"] == ["(_.amount >= 5)", "amount <= 100"]
    assert not sv.verify(
        "select id, amount - 5 as rest from orders",
        tables={"orders": orders},
        requires={"orders": [_.amount >= 4]},
        ensures=[_.rest >= 0],
        counterexamples=0,
    ).proved


def test_report_runs_the_plan_it_checked():
    # #461: verify, then run exactly that plan, for Ibis and for SQL.
    import pyarrow as pa

    con = sv.connect("duckdb")
    con.put("t", pa.table({"host": ["a", "a", "b"], "cpu": [1, 5, 7]}))
    t = con.table("t")
    expected = [{"host": "a", "m": 5}, {"host": "b", "m": 7}]
    ibis_q = t.filter(_.cpu > 3).group_by("host").agg(m=_.cpu.max())
    sql_q = "SELECT host, max(cpu) AS m FROM t WHERE cpu > 3 GROUP BY host"
    for report in (
        sv.verify(ibis_q, ensures=[sv.unique("host")]),
        sv.verify(sql_q, tables={"t": t}, ensures=[sv.unique("host")]),
    ):
        assert report.proved
        assert report.plan is not None
        for engine in (None, "polars"):
            assert report.run(con, engine).sort_by("host").to_pylist() == expected


def test_report_runs_with_its_params():
    import pyarrow as pa

    con = sv.connect("duckdb")
    con.put("t", pa.table({"cpu": [1, 5, 7]}))
    t = con.table("t")
    p = ibis.param(ibis.dtype("int64"))
    report = sv.verify(t.filter(_.cpu > p), params={p: 4})
    assert sorted(report.run(con).column("cpu").to_pylist()) == [5, 7]


def test_report_without_plan_refuses_to_run():
    with pytest.raises(ValueError, match="no plan"):
        sv.Report(requires={}, ensures=[]).run(sv.connect())


def test_non_nullable_schema_is_used():
    strict = ibis.table({"id": "!int64", "amount": "int64"}, name="strict")
    assert sv.verify(strict.select("id"), ensures=[_.id.notnull()]).proved
    assert not sv.verify(strict.select("amount"), ensures=[_.amount.notnull()]).proved


def test_preconditions_are_checked_on_data():
    with pytest.raises(PreconditionError, match="amount >= 0"):
        doubled(bound_orders([(1, "ada", -3)]))
    doubled(bound_orders([(1, "ada", 30)]))


def test_runtime_fallback_checks_unproved_postconditions():
    @sv.transform(ensures=[_.amount < 100], on_unproved="check")
    def passthrough(orders):
        return orders.select(orders.amount)

    passthrough(bound_orders([(1, "ada", 30)]))
    with pytest.raises(PostconditionError):
        passthrough(bound_orders([(1, "ada", 300)]))


def test_checks_on_data_do_not_warn_through_pandas():
    # Ibis 12 converts `execute()`'s scalar through pandas, which warns under
    # pandas 3.1 (#479): the counts are fetched through Arrow.
    pandas_errors = pytest.importorskip("pandas.errors")
    with warnings.catch_warnings():
        warnings.simplefilter("error", getattr(pandas_errors, "Pandas4Warning", FutureWarning))
        warnings.filterwarnings("error", message="The 'future.infer_string' option")
        con = sv.connect()
        schema = ibis.schema({"id": "int64", "amount": "int64"})
        create_table(con, "orders_479", schema, [(1, 30), (1, 300)])

        @sv.transform(ensures=[_.amount < 100], on_unproved="check")
        def passthrough(orders):
            return orders.select("id", "amount")

        with pytest.raises(PostconditionError):
            passthrough(con.table("orders_479")).to_pyarrow()
        t = con.table("orders_479")
        assert violations(t, sv.unique("id")) == 1
        assert violations(t, sv.max_rows(1)) == 1
        assert violations(t, _.amount < 100) == 1


# Soundness on data: whatever Lean proves must hold on any input that satisfies
# the preconditions.
CONTRACTS = [
    (
        {"orders": [_.amount >= 0, _.id.notnull()]},
        lambda o: o.filter(o.amount > 10).select(o.id, d=o.amount * 2 - 3),
        [_.d > 15, _.d.notnull(), _.id.notnull(), _.d >= 19, _.d > 19, _.d != 0, _.d == 19],
    ),
    (
        {"orders": [_.amount <= 50]},
        lambda o: o.filter(o.amount >= -5).select(n=-o.amount, s=o.amount - 7),
        [_.n >= -50, _.n <= 5, _.s <= 43, _.s >= -12, _.n.notnull(), _.n > -50],
    ),
    (
        {"orders": []},
        lambda o: o.filter(o.amount == 7).select(z=o.amount * 0, e=o.amount),
        [_.z == 0, _.e == 7, _.e != 8, _.e == 8, _.z != 0],
    ),
]
amounts = st.one_of(st.none(), st.integers(-100, 100))


@pytest.mark.parametrize("engine", ["datafusion", "duckdb"])
@pytest.mark.parametrize("index", range(len(CONTRACTS)))
@settings(max_examples=25, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(data=st.data())
def test_proved_postconditions_hold_on_data(index, engine, data):
    requires, make, ensures = CONTRACTS[index]
    report = sv.verify(make(orders), requires=requires, ensures=ensures)
    assert any(c.proved for c in report.ensures)
    rows = data.draw(st.lists(st.tuples(st.integers(0, 5) | st.none(), st.just("ada"), amounts)))
    table = bound_orders(rows)
    rows_ok = all(violations(table, c, engine) == 0 for c in requires["orders"])
    if not rows_ok:
        return
    result = make(table)
    for cond, checked in zip(ensures, report.ensures, strict=True):
        if checked.proved:
            assert violations(result, cond, engine) == 0, checked.label


# IoT: per-sensor cleaning, a wide join on time, and a two-step window.
ERR, STEP = -9999, 60
sensor1 = ibis.table({"ts": "int64", "value": "int64"}, name="sensor1")
sensor2 = ibis.table({"ts": "int64", "value": "int64"}, name="sensor2")


def iot_windows(s1, s2):
    a = s1.filter((s1.value != ERR) & s1.value.notnull())
    b = s2.filter((s2.value != ERR) & s2.value.notnull())
    wide = a.join(b, a.ts == b.ts).select(ts=a.ts, s1=a.value, s2=b.value)
    w0, w1 = wide.view(), wide.view()
    return w0.join(w1, w1.ts == w0.ts + STEP).select(
        t0=w0.ts, t1=w1.ts, a0=w0.s1, a1=w1.s1, b0=w0.s2, b1=w1.s2
    )


IOT_ENSURES = [
    _.t1 - _.t0 == STEP,
    _.t1 > _.t0,
    _.t0.notnull(),
    _.a0 != ERR,
    _.a1 != ERR,
    _.b0 != ERR,
    _.b1.notnull(),
    _.t1 - _.t0 == 2 * STEP,  # wrong on purpose
]


def test_iot_windows_are_proved_complete_and_consecutive():
    report = sv.verify(iot_windows(sensor1, sensor2), ensures=IOT_ENSURES)
    assert [c.proved for c in report.ensures] == [True] * 7 + [False]
    assert report.ensures[-1].value == "FALSE"


@settings(max_examples=25, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(data=st.data())
def test_iot_proved_postconditions_hold_on_data(data):
    readings = st.lists(
        st.tuples(st.sampled_from([0, 60, 120, 180, 300]), st.sampled_from([None, ERR, 1, 7, 42])),
        max_size=8,
    )
    db = sv.connect()
    for name in ["sensor1", "sensor2"]:
        create_table(db, name, sensor1.schema(), data.draw(readings))
    report = sv.verify(iot_windows(sensor1, sensor2), ensures=IOT_ENSURES)
    result = iot_windows(db.table("sensor1"), db.table("sensor2"))
    for cond, checked in zip(IOT_ENSURES, report.ensures, strict=True):
        if checked.proved:
            assert violations(result, cond) == 0, checked.label


KEYS = {"sensor1": [sv.unique("ts")], "sensor2": [sv.unique("ts")]}


def test_keys_flow_through_joins_and_windows():
    report = sv.verify(
        iot_windows(sensor1, sensor2),
        requires=KEYS,
        ensures=[sv.unique("t0"), sv.unique("t0", "a0"), sv.unique("a0")],
    )
    assert [c.proved for c in report.ensures] == [True, True, False]
    # Without a key on sensor2, duplicate readings could duplicate windows.
    report = sv.verify(
        iot_windows(sensor1, sensor2),
        requires={"sensor1": [sv.unique("ts")]},
        ensures=[sv.unique("t0")],
    )
    assert not report.proved


def test_unique_precondition_is_checked_on_data():
    @sv.transform(requires={"orders": [sv.unique("id")]}, ensures=[sv.unique("id")])
    def big(orders):
        return orders.filter(orders.amount > 10)

    with pytest.raises(PreconditionError, match="unique"):
        big(bound_orders([(1, "ada", 30), (1, "bob", 40)]))
    big(bound_orders([(1, "ada", 30), (2, "bob", 40)]))
    assert big.report is not None and big.report.proved


@settings(max_examples=25, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(data=st.data())
def test_proved_keys_hold_on_data(data):
    readings = st.lists(
        st.tuples(st.sampled_from([0, 60, 120, 180, 240]), st.sampled_from([None, ERR, 1, 7])),
        max_size=5,
        unique_by=lambda r: r[0],
    )
    db = sv.connect()
    for name in ["sensor1", "sensor2"]:
        create_table(db, name, sensor1.schema(), data.draw(readings))
    result = iot_windows(db.table("sensor1"), db.table("sensor2"))
    assert violations(result, sv.unique("t0")) == 0


# -- hints that name the bound to add (#379) ------------------------------------


SAMPLES = ibis.table(
    {"host": "string", "ts": "timestamp", "day": "date", "cpu": "int64"}, name="samples"
)


@pytest.mark.parametrize(
    ("expr", "col", "low", "high"),
    [
        (
            SAMPLES.select(m=SAMPLES.ts.truncate("m")),
            "ts",
            datetime(2000, 1, 1),
            datetime(2100, 1, 1),
        ),
        (SAMPLES.select(m=SAMPLES.day.truncate("M")), "day", date(2000, 1, 1), date(2100, 1, 1)),
    ],
)
def test_a_truncation_hint_names_the_bounds_that_clear_it(expr, col, low, high):
    # Inferred (#244), needed by default (#655); without inference, the
    # issue's hint names them.
    assert sv.verify(expr, on_inferred="ignore").proved
    assert not sv.verify(expr).proved
    report = sv.verify(expr, on_inferred="off")
    [issue] = report.errors
    assert issue.kind == "overflow" and issue.hint is not None
    hint = issue.hint
    assert f"`(_.{col} >= " in hint and "the requires of 'samples'" in hint
    assert OVERFLOW_HINT not in str(report)  # the hint covers the overflow
    bounded = sv.verify(expr, requires={"samples": [_[col] >= low, _[col] < high]})
    assert not bounded.issues


def test_a_sum_hint_proposes_a_bound_and_the_largest_group():
    expr = SAMPLES.group_by("host").aggregate(total=_.cpu.sum())
    [hint] = sv.verify(expr).hints
    assert hint.startswith("SUM of `cpu`: bound it in `requires` of samples")
    assert "`_.cpu <= 1_000_000_000` and `_.cpu >= -1_000_000_000`" in hint
    assert "up to 9,223,372,036 rows" in hint
    [hint] = sv.verify(expr, requires={"samples": [_.cpu >= 0, _.cpu <= 100]}).hints
    assert "it is in [0, 100]" in hint and "up to 92,233,720,368,547,758 rows" in hint
    assert "`sv.max_rows(92_233_720_368_547_758)` in `requires` of samples proves it" in hint
    # With that row cap, the sum is proved to fit.
    cap = sv.max_rows(92_233_720_368_547_758)
    proved = sv.verify(expr, requires={"samples": [_.cpu >= 0, _.cpu <= 100, cap]})
    assert not proved.issues and not proved.assumed


def test_an_overflow_of_two_columns_suggests_a_split():
    report = sv.verify(SAMPLES.select(d=SAMPLES.cpu * SAMPLES.cpu))
    [issue] = report.errors
    assert issue.hint is not None and issue.hint.startswith("no single bound rules it out")
    assert report.inferred == {} and not report.hints
    assert OVERFLOW_HINT not in str(report)


def test_a_date_beyond_year_9999_is_described_without_overflow():
    # A DATE cast from a TIMESTAMP ranges past what Python's `date` holds (#435).
    jobs = ibis.table({"started_at": "!timestamp"}, name="jobs")
    sql = "SELECT CAST(started_at AS DATE) AS day, count(*) AS n FROM jobs GROUP BY day"
    facts = sv.verify(sql, tables={"jobs": jobs.schema()}).facts
    assert facts["day"] == "any date"


def test_sql_facts_describe_timestamps_and_dates():
    # The lift knows the SQL's types: no integer codes in the facts (#452).
    t = ibis.table({"host": "string", "minute": "timestamp", "day": "date"}, name="t")
    facts = sv.verify("SELECT host, minute, day FROM t", tables={"t": t.schema()}).facts
    assert facts == sv.verify(t.select("host", "minute", "day")).facts
    assert facts["minute"] == "any timestamp or NULL"
    assert facts["day"] == "any date or NULL"
    bounded = sv.verify(
        "SELECT minute FROM t WHERE minute >= TIMESTAMP '2026-01-01 00:00:00'",
        tables={"t": t.schema()},
    ).facts
    assert bounded["minute"] == "a timestamp ≥ 2026-01-01 00:00:00"

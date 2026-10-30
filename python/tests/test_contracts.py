"""Contracts: postconditions are proved from preconditions, or refused."""

import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.contracts import violations
from sverify.examples import customers, orders


@sv.transform(
    requires={"orders": [_.amount >= 0, _.id.notnull()]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL", _.doubled > 20],
)
def doubled(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


def test_postconditions_are_proved():
    doubled(orders)
    report = doubled.last_report
    assert report is not None
    assert report.proved
    assert report.facts["doubled"] == "an integer ≥ 22"
    assert report.facts["id"] == "any integer"  # never NULL, by the precondition


def test_unprovable_postcondition_is_refused():
    @sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
    def plus_one(orders):
        return orders.select(orders.id, total=orders.amount + 1)

    with pytest.raises(sv.VerificationError) as e:
        plus_one(orders)
    assert e.value.report.unproved[0].value == "TRUE or FALSE"
    assert e.value.report.facts["total"] == "an integer ≥ 1"


def test_null_propagates_unless_ruled_out():
    # Without a precondition, `amount + 1` can be NULL...
    report = sv.verify(orders.select(t=orders.amount + 1), ensures=[_.t.notnull()])
    assert not report.proved
    # ...and a filter on `amount` rules that out (NULL > 0 is not TRUE).
    report = sv.verify(
        orders.filter(orders.amount > 0).select(t=orders.amount + 1), ensures=[_.t.notnull()]
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


def test_non_nullable_schema_is_used():
    strict = ibis.table({"id": "!int64", "amount": "int64"}, name="strict")
    assert sv.verify(strict.select("id"), ensures=[_.id.notnull()]).proved
    assert not sv.verify(strict.select("amount"), ensures=[_.amount.notnull()]).proved


def bound_orders(rows):
    con = sv.connect()
    sv.create_table(con, "orders", orders.schema(), rows)
    return con.table("orders")


def test_preconditions_are_checked_on_data():
    with pytest.raises(sv.PreconditionError, match="amount >= 0"):
        doubled(bound_orders([(1, "ada", -3)]))
    doubled(bound_orders([(1, "ada", 30)]))


def test_runtime_fallback_checks_unproved_postconditions():
    @sv.transform(ensures=[_.amount < 100], on_unproved="runtime")
    def passthrough(orders):
        return orders.select(orders.amount)

    passthrough(bound_orders([(1, "ada", 30)]))
    with pytest.raises(sv.PostconditionError):
        passthrough(bound_orders([(1, "ada", 300)]))


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
        sv.create_table(db, name, sensor1.schema(), data.draw(readings))
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

    with pytest.raises(sv.PreconditionError, match="unique"):
        big(bound_orders([(1, "ada", 30), (1, "bob", 40)]))
    big(bound_orders([(1, "ada", 30), (2, "bob", 40)]))
    assert big.last_report is not None and big.last_report.proved


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
        sv.create_table(db, name, sensor1.schema(), data.draw(readings))
    result = iot_windows(db.table("sensor1"), db.table("sensor2"))
    assert violations(result, sv.unique("t0")) == 0

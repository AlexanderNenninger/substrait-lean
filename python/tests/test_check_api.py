"""The report API for tools that read a contract's proof without running
it (an editor, `dbt`, CI): `ContractedTransform.check`, `Report.inputs`,
`Report.route`, `Report.notes` and the `message` of each finding."""

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify.errors import VerificationError

SCHEMA = {"id": "int64", "amount": "int64", "qty": "int64"}


@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.unit >= 0])
def unit(orders):
    return orders.select(orders.id, unit=orders.amount // orders.qty)


@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000]},
    ensures=[_.doubled >= 0],
)
def doubled(orders):
    return orders.select(orders.id, doubled=orders.amount * 2)


def test_contracted_transform_is_exported() -> None:
    assert isinstance(unit, sv.ContractedTransform)


def test_check_returns_an_unproved_report_without_raising() -> None:
    with pytest.raises(VerificationError):
        unit(ibis.table(SCHEMA, name="orders"))
    report = unit.check(orders=SCHEMA)
    assert not report.proved
    assert report.needed == {"orders": ["(_.qty != 0)"]}
    assert unit.last_report is report


def test_check_takes_schemas_tables_and_positions() -> None:
    by_name = doubled.check(orders=ibis.schema(SCHEMA))
    by_position = doubled.check(ibis.table(SCHEMA, name="anything"))
    assert by_name.proved and by_position.proved
    assert by_position.inputs == {"orders": ibis.schema(SCHEMA)}


def test_check_reads_no_data() -> None:
    con = sv.connect()
    con.put("orders", pa.table({"id": [1], "amount": [-5], "qty": [1]}))
    # The precondition amount >= 0 fails on the data; check does not read it.
    assert doubled.check(con.table("orders")).proved


def test_check_counterexamples() -> None:
    assert unit.check(orders=SCHEMA, counterexamples=0).ensures[0].counterexample is None
    assert unit.check(orders=SCHEMA).ensures[0].counterexample is not None


def test_check_refuses_what_is_no_table() -> None:
    with pytest.raises(TypeError, match="orders must be an Ibis table or a schema"):
        unit.check(orders=3)
    with pytest.raises(TypeError):
        unit.check(customers=SCHEMA)


def test_inputs_of_a_sql_report() -> None:
    orders = ibis.table(SCHEMA, name="orders")
    report = sv.verify("select id, amount from orders", tables={"orders": orders})
    assert report.inputs == {"orders": ibis.schema(SCHEMA)}
    assert set(report.output) == {"id", "amount"}


def test_route_without_a_run() -> None:
    report = doubled.check(orders=SCHEMA)
    route = report.route("duckdb")
    assert route.cls == "exact" and not route.refused
    assert report.routes == {}  # nothing ran
    refused = unit.check(orders=SCHEMA).route("duckdb")
    assert refused.refused and refused.reason.startswith("not verified")


def test_messages_are_the_lines_of_the_report() -> None:
    report = unit.check(orders=SCHEMA, counterexamples=0)
    [c] = report.ensures
    assert c.message.startswith("NOT proved: it may be FALSE or NULL")
    assert f"ensures {c.label}: {c.message}" in str(report)
    t = ibis.table({"k": "string", "x": "int64"}, name="t")
    summed = sv.verify(t.group_by("k").aggregate(s=t.x.sum()), counterexamples=0)
    [assumed] = summed.assumed
    assert assumed.assumption.startswith("SUM of x fits 64 bits")
    assert f"assumes: {assumed.assumption}" in str(summed)
    raising = sv.verify(t.select(r=t.x // 0), on_inferred="silent", counterexamples=0)
    for issue in raising.errors:
        assert f"may fail: {issue.message}" in str(raising)


def test_notes() -> None:
    t = ibis.table({"k": "int64", "ts": "int64", "v": "float64"}, name="t")
    w = ibis.window(group_by="k", order_by="ts")
    report = sv.verify(t.mutate(p=t.v.lag(1).over(w)), counterexamples=0)
    assert not report.deterministic
    assert report.notes and report.notes[0].startswith("rows may tie")
    assert all(f"note: {n}" in str(report) for n in report.notes)
    assert doubled.check(orders=SCHEMA).notes == []


def test_issue_suggested_is_the_hint_as_data() -> None:
    t = ibis.table({"a": "int64", "b": "int64"}, name="t")
    report = sv.verify(t.select(r=t.a // t.b), on_inferred="off", counterexamples=0)
    by_kind = {i.kind: i for i in report.errors}
    zero = by_kind["division by zero"]
    assert zero.suggested == {"t": ("(_.b != 0)",)}
    assert zero.hint == "state `(_.b != 0)` in the requires of 't'"
    fixed = sv.verify(
        t.select(r=t.a // t.b),
        requires={"t": [_.b != 0, _.a >= -9 * 10**18]},
        on_inferred="off",
        counterexamples=0,
    )
    assert not fixed.errors


def test_counterexamples_from_the_environment(monkeypatch) -> None:
    from sverify.contracts import default_counterexamples

    assert default_counterexamples() == 200
    monkeypatch.setenv("SVERIFY_COUNTEREXAMPLES", "0")
    assert default_counterexamples() == 0
    t = ibis.table(SCHEMA, name="orders")
    report = sv.verify(t.select(t.id), ensures=[_.id > 0])
    assert report.ensures[0].counterexample is None
    assert unit.check(orders=SCHEMA).ensures[0].counterexample is None
    assert unit.check(orders=SCHEMA, counterexamples=200).ensures[0].counterexample is not None
    monkeypatch.setenv("SVERIFY_COUNTEREXAMPLES", "many")
    with pytest.raises(ValueError, match="must be an integer"):
        sv.verify(t.select(t.id))

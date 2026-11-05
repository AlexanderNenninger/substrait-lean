"""Inferred bounds against overflow (#244): Lean's backward range analysis
(`SubstraitLean/Infer.lean`) proposes them, the unchanged contract proof
checks them, and they behave like `requires` on data and metadata."""

from datetime import datetime

import ibis
import pyarrow as pa
import pytest
from deltalake import write_deltalake
from ibis import _

import sverify as sv
import sverify.contracts as contracts
from _pipelines import discharged, make_orders, orders_table, paid
from sverify.contracts import ON_DATA, Inferred, label
from sverify.engine import create_table
from sverify.errors import PreconditionError, VerificationError
from sverify.io import StaticSource

T = ibis.table(
    {"id": "int64", "amount": "int64", "b": "int64", "ts": "timestamp", "d": "date", "q": "int32"},
    name="orders",
)


def inferred(report) -> list[str]:
    return [label(c) for cs in report.inferred.values() for c in cs]


# -- the analysis, on the issue's examples ---------------------------------------


@pytest.mark.parametrize(
    ("expr", "requires", "bounds"),
    [
        # `amount * 2` on BIGINT fits when amount < 2⁶²; `amount >= 0` is given.
        (T.select(x=T.amount * 2), [_.amount >= 0], ["(_.amount < 2**62)"]),
        (T.select(x=T.amount * 2), [], ["(_.amount >= -2**62)", "(_.amount < 2**62)"]),
        # Chains: rounded inward to a round number.
        (T.select(x=T.amount * 3 + 1), [_.amount >= 0], ["(_.amount < 3 * 10**18)"]),
        (T.select(x=(T.amount - 5) * -4), [_.amount >= 0], ["(_.amount < 2**61)"]),
        # A sum with a value the preconditions already bound.
        (
            T.select(x=T.amount + T.b),
            [_.amount >= 0, _.b >= 0, _.b <= 1000],
            ["(_.amount < 9 * 10**18)"],
        ),
        # A product with a bounded column.
        (
            T.select(x=T.amount * T.b),
            [_.b >= -10, _.b <= 10],
            ["(_.amount >= -9 * 10**17)", "(_.amount < 9 * 10**17)"],
        ),
        # Negation and ABS fail on the smallest BIGINT only.
        (T.select(x=-T.amount), [], ["(_.amount >= -9 * 10**18)"]),
        (T.select(x=T.amount.abs()), [], ["(_.amount >= -9 * 10**18)"]),
        # Narrower integers at their width.
        (T.select(x=T.q * 2), [], ["(_.q >= -2**30)", "(_.q < 2**30)"]),
        # Timestamp truncation (#379): to whole years.
        (
            T.select(x=T.ts.truncate("M")),
            [],
            ["(_.ts >= datetime(1678, 1, 1))", "(_.ts < datetime(2262, 1, 1))"],
        ),
        (T.select(x=T.ts.truncate("m")), [], ["(_.ts >= datetime(1, 1, 1))"]),
        (
            T.select(x=T.d.truncate("Y")),
            [],
            ["(_.d >= date(1679, 1, 1))", "(_.d < date(2262, 1, 1))"],
        ),
        # Through a filter and a projection, to the base column.
        (
            T.filter(T.amount > 10).select(y=_.amount + 1).select(z=_.y * 2),
            [_.amount >= 0],
            ["(_.amount < 4 * 10**18)"],
        ),
        # MIN and MAX are values of their argument.
        (
            T.group_by("id").aggregate(m=T.amount.max()).select(x=_.m * 2),
            [_.amount >= 0],
            ["(_.amount < 2**62)"],
        ),
    ],
)
def test_inferred_bounds_prove_the_contract(expr, requires, bounds):
    report = sv.verify(expr, requires={"orders": requires}, ensures=[])
    assert report.proved, report
    assert inferred(report) == bounds
    # They are assumed like the rest of `requires`, and shown as inferred.
    assert all(b in report.requires["orders"] for b in bounds)
    assert f"requires orders: {bounds[0]} (inferred" in str(report)
    assert "assumed (inferred)" in report._repr_markdown_()


@pytest.mark.parametrize(
    ("dtype", "bounds"),
    [
        ("int8", ["(_.v >= -127)", "(_.v <= 127)"]),
        ("int16", ["(_.v >= -32_767)", "(_.v <= 32_767)"]),
        ("int32", ["(_.v >= -2 * 10**9)", "(_.v <= 2_147_483_647)"]),
        ("int64", ["(_.v >= -9 * 10**18)"]),
    ],
)
def test_abs_of_a_narrow_integer_is_bounded_within_its_type(dtype, bounds):
    """`ABS` fails on the smallest value of the column's type, not only of
    BIGINT's, and no bound reaches 2**63, which the lift reads as a HUGEINT
    (#616)."""
    report = sv.verify("SELECT abs(v) AS a FROM t", tables={"t": {"v": dtype}})
    assert report.proved, report
    assert inferred(report) == bounds


def test_abs_of_the_smallest_tinyint_may_fail():
    report = sv.verify("SELECT abs(v) AS a FROM t", tables={"t": {"v": "int8"}}, infer=False)
    assert not report.proved
    assert any("WRAP8" in str(i) for i in report.errors), report


def test_without_inference_the_hint_names_the_bound():
    report = sv.verify(T.select(x=T.amount * 2), requires={"orders": [_.amount >= 0]}, infer=False)
    assert not report.proved
    assert report.inferred == {}
    [issue] = report.errors
    assert issue.hint == "state `(_.amount < 2**62)` in the requires of 'orders'"
    assert "hint: state `(_.amount < 2**62)`" in str(report)


@pytest.mark.parametrize(
    ("expr", "hint"),
    [
        # Two unbounded columns have no unique weakest bound: suggested, not assumed.
        (
            T.select(x=T.amount * T.b),
            "no single bound rules it out; for example, state `(_.amount < 3 * 10**9)`, "
            "`(_.b >= -3 * 10**9)`, `(_.b < 3 * 10**9)` in the requires of 'orders'",
        ),
        (
            T.select(x=T.amount + T.b),
            "no single bound rules it out; for example, state `(_.amount < 2**62)`, "
            "`(_.b >= -2**62)`, `(_.b < 2**62)` in the requires of 'orders'",
        ),
        # A sum's size depends on the group's.
        (
            T.group_by("id").aggregate(s=T.amount.sum()).select(x=_.s * 2),
            "no bound on an input column rules it out: it reads the value "
            "of an aggregate other than MIN or MAX",
        ),
    ],
)
def test_limits_are_suggested_not_assumed(expr, hint):
    report = sv.verify(expr, requires={"orders": [_.amount >= 0]})
    assert not report.proved
    assert report.inferred == {}
    assert any(i.hint == hint for i in report.errors), report.errors


def test_a_wrong_inference_fails_the_proof(monkeypatch):
    """The inference is untrusted: a bound too weak to rule out the overflow
    is assumed, and the proof with it still fails."""

    def too_weak(needs, schemas):
        return {"orders": [Inferred('"amount" < 9000000000000000000', "(_.amount < 9 * 10**18)")]}

    monkeypatch.setattr(contracts, "_render_needs", too_weak)
    report = sv.verify(T.select(x=T.amount * 2), requires={"orders": [_.amount >= 0]})
    assert inferred(report) == ["(_.amount < 9 * 10**18)"]
    assert not report.proved
    assert [i.kind for i in report.errors] == ["overflow"]


def test_values_from_upstream_are_suggested_for_its_ensures():
    @sv.transform(requires={"t": [_.amount >= 0]}, ensures=[_.twice >= 0])
    def twice(t):
        return t.select(t.id, twice=t.amount * 2)

    src = StaticSource(pa.table({"id": [1], "customer": ["a"], "amount": [5]}), name="orders")
    with pytest.raises(VerificationError) as e:
        paid_without_bound(src).pipe(twice)
    [issue] = e.value.report.errors
    assert issue.hint == "state `(_.amount < 2**62)` in the ensures of 'paid_without_bound'"


@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.amount >= 0, _.amount.notnull()])
def paid_without_bound(orders):
    return orders.filter(orders.amount.notnull())


# -- like `requires`: checked on data, proved from metadata, composed ----------


@sv.transform(
    requires={"orders": [_.amount >= 0, _.id.notnull()]},
    ensures=[_.doubled >= 0, _.doubled.notnull()],
)
def doubled(orders):
    return orders.filter(orders.amount.notnull()).select(orders.id, doubled=orders.amount * 2)


def test_bound_inputs_are_checked_at_call():
    db = sv.connect()
    schema = ibis.schema({"id": "int64", "amount": "int64"})
    create_table(db, "ok", schema, [(1, 7)])
    doubled(db.table("ok"))
    assert [str(p) for p in doubled.last_preconditions][-1] == (
        "orders: (_.amount < 2**62) (inferred, checked on data)"
    )
    create_table(db, "big", schema, [(1, 2**62)])
    with pytest.raises(
        PreconditionError, match=r"1 row\(s\) of orders violate \(_.amount < 2\*\*62\)"
    ):
        doubled(db.table("big"))


def test_an_eager_table_gets_the_inferred_bound():
    """#430: a memtable is not a named base table, yet its bound is inferred,
    checked on its data, and named as a `requires` in hints."""

    def double(orders):
        return orders.mutate(doubled=_.amount * 2)

    contract = {"requires": {"orders": [_.amount >= 0]}, "ensures": [_.doubled >= 0]}
    mutated = sv.transform(**contract)(double)

    orders = ibis.memtable(pa.table({"id": [1, 2], "amount": pa.array([10, 20], pa.int64())}))
    out = mutated(orders)
    report = mutated.last_report
    assert report is not None and report.proved
    assert inferred(report) == ["(_.amount < 2**62)"]
    assert discharged(mutated.last_preconditions)[("orders", "(_.amount < 2**62)")] == ON_DATA
    assert sorted(out.to_pyarrow().column("doubled").to_pylist()) == [20, 40]
    big = ibis.memtable(pa.table({"id": [1], "amount": pa.array([2**62 + 5], pa.int64())}))
    with pytest.raises(
        PreconditionError, match=r"1 row\(s\) of orders violate \(_.amount < 2\*\*62\)"
    ):
        mutated(big)
    explicit = sv.transform(**contract, infer=False)(double)
    with pytest.raises(VerificationError, match=r"in the requires of 'orders'"):
        explicit(orders)


def test_refresh_checks_the_inferred_bound_on_data():
    src = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders")
    node = src.pipe(doubled)
    first = node.refresh()["doubled"]
    assert discharged(first.preconditions)[("orders", "(_.amount < 2**62)")] == ON_DATA
    assert "requires orders: (_.amount < 2**62) (inferred, checked on data)" in str(first)
    assert sorted(node.to_arrow().to_pylist(), key=lambda r: r["id"]) == [
        {"id": 1, "doubled": 60},
        {"id": 2, "doubled": 10},
    ]
    big = StaticSource(pa.table({"id": [1], "amount": [2**62 + 5]}), name="huge")
    with pytest.raises(
        PreconditionError, match=r"1 row\(s\) of huge violate \(_.amount < 2\*\*62\)"
    ):
        big.pipe(doubled).refresh()


def test_metadata_proves_the_inferred_bound(tmp_path):
    """Delta file statistics (max(amount) = 1200) prove the bound, on the
    first refresh and on each batch."""
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 1200)])
    node = src.pipe(doubled)
    found = discharged(node.refresh()["doubled"].preconditions)
    assert found[("orders", "(_.amount < 2**62)")] == "file stats @v1"
    write_deltalake(src.uri, orders_table([(3, "cy", 50)]), mode="append")
    report = node.refresh()["doubled"].report
    assert report is not None
    found = discharged(report.preconditions)
    assert found[("orders", "(_.amount < 2**62)")] == "file stats @v2 (new files)"


def test_inferred_bounds_compose_through_nodes():
    """A bound inferred on a source holds for every node after it, which
    checks it at refresh; a bound an upstream contract guarantees needs no
    inference."""

    @sv.transform(requires={"t": [_.doubled >= 0]}, ensures=[_.id.notnull()])
    def ids(t):
        return t.filter(t.id.notnull()).select(t.id)

    src = StaticSource(pa.table({"id": [1], "amount": [3]}), name="orders")
    node = src.pipe(doubled).pipe(ids)
    found = discharged(node.refresh()["ids"].preconditions)
    assert found[("orders", "(_.amount < 2**62)")] == ON_DATA
    assert node.to_arrow().to_pylist() == [{"id": 1}]

    @sv.transform(requires={"t": [_.amount >= 0]}, ensures=[_.twice >= 0])
    def twice(t):
        return t.select(t.id, twice=t.amount * 2)

    shop = StaticSource(pa.table({"id": [1], "customer": ["a"], "amount": [5]}), name="orders")
    paid(shop).pipe(twice)  # `paid` guarantees `amount < 1_000_000_000`
    assert twice.last_report is not None
    assert twice.last_report.proved and twice.last_report.inferred == {}


def test_strict_requires_explicit_bounds():
    @sv.transform(requires={"orders": [_.amount >= 0]}, infer=False)
    def strictly(orders):
        return orders.select(x=orders.amount * 2)

    src = StaticSource(pa.table({"id": [1], "amount": [3]}), name="orders")
    with pytest.raises(VerificationError, match=r"overflow: amount \* 2") as e:
        src.pipe(strictly)
    assert e.value.report.inferred == {}
    [issue] = e.value.report.errors
    assert issue.hint == "state `(_.amount < 2**62)` in the requires of 'orders'"

    @sv.transform(requires={"orders": [_.amount >= 0, _.amount < 2**62]}, infer=False)
    def stated(orders):
        return orders.select(x=orders.amount * 2)

    src.pipe(stated)
    assert stated.last_report is not None and stated.last_report.proved


def test_datetime_bound_is_checked_on_data():
    @sv.transform(ensures=[_.m.notnull()], requires={"ev": [_.ts.notnull()]})
    def per_month(ev):
        return ev.select(m=ev.ts.truncate("M"))

    ok = StaticSource(pa.table({"ts": [datetime(2024, 5, 3)]}), name="ev")
    node = ok.pipe(per_month)
    assert inferred(per_month.last_report) == [
        "(_.ts >= datetime(1678, 1, 1))",
        "(_.ts < datetime(2262, 1, 1))",
    ]
    node.refresh()
    assert node.to_arrow().to_pylist() == [{"m": datetime(2024, 5, 1)}]
    late = StaticSource(pa.table({"ts": [datetime(2300, 1, 1)]}), name="late")
    with pytest.raises(PreconditionError, match=r"datetime\(2262, 1, 1\)"):
        late.pipe(per_month).refresh()


def test_null_passes_an_inferred_bound():
    """Only a value can overflow, so NULL meets an inferred bound."""

    @sv.transform()
    def twice(t):
        return t.select(x=t.amount * 2)

    db = sv.connect()
    create_table(db, "nulls", ibis.schema({"amount": "int64"}), [(None,), (3,)])
    twice(db.table("nulls"))
    assert [p.condition for p in twice.last_preconditions] == [
        "(_.amount >= -2**62)",
        "(_.amount < 2**62)",
    ]

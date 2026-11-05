"""`on_inferred=` (#655): a precondition sverify infers is an error by
default, assumed with a warning on "warn", assumed silently on "silent"."""

import warnings

import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify.contracts import InferredPreconditionWarning
from sverify.errors import PreconditionError, RouteError, VerificationError
from sverify.io import StaticSource


def _needed(report):
    """The labels of `report.needs` per input table."""
    out: dict[str, list[str]] = {}
    for n in report.needs:
        out.setdefault(n.table, []).append(n.label)
    return out



@pytest.fixture
def con():
    c = sv.connect()
    c.put("t", pa.table({"k": ["a", "b"], "qty": [1, 0], "total": [10, 20]}))
    return c


def test_an_inferred_precondition_is_an_error_by_default(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select(t.k, per=t.total // t.qty))
    assert not report.proved
    assert _needed(report) == {"t": ["(_.total >= -9 * 10**18)", "(_.qty != 0)"]}
    text = str(report)
    assert (
        "needs: (_.total >= -9 * 10**18) and (_.qty != 0) on t, inferred from `total // qty` "
        "(overflow or division by zero otherwise): declare them in requires (each run then "
        "checks them on the data), or rewrite so no row needs them "
        "(`t.filter((_.total >= -9 * 10**18) & (_.qty != 0))` first, or a CASE)"
    ) in text
    assert "requires t: (_.qty != 0)" not in text
    md = report._repr_markdown_()
    assert "needs | ❌ (_.total >= -9 * 10**18) and (_.qty != 0) on t" in md
    assert "assumed (inferred)" not in md


def test_the_refusal_names_both_fixes(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select(t.k, per=t.total // t.qty))
    with pytest.raises(
        RouteError,
        match=r"not verified: needs .*declare them in requires.*filter.*\(see report.needs\)",
    ):
        report.run(con)


def test_declaring_it_proves_the_plan_and_checks_it(con) -> None:
    t = con.table("t")
    report = sv.verify(
        t.select(t.k, per=t.total // t.qty),
        requires={"t": [_.qty != 0, _.total >= 0]},
    )
    assert report.proved and _needed(report) == {}
    with pytest.raises(PreconditionError, match=r"violate \(_.qty != 0\)"):
        report.run(con)


def test_filtering_first_needs_no_precondition(con) -> None:
    t = con.table("t")
    kept = t.filter(t.qty != 0)
    report = sv.verify(
        kept.select(kept.k, per=kept.total // kept.qty), requires={"t": [_.total >= 0]}
    )
    assert report.proved
    assert report.run(con).to_pylist() == [{"k": "a", "per": 10}]


def test_warn_and_silent_assume_it(con) -> None:
    t = con.table("t")
    expr = t.select(t.k, per=t.total // t.qty)
    with pytest.warns(InferredPreconditionWarning, match=r"\(_.qty != 0\) on t, inferred from"):
        warned = sv.verify(expr, on_inferred="warn")
    assert warned.proved and _needed(warned) == {}
    with warnings.catch_warnings():
        warnings.simplefilter("error", InferredPreconditionWarning)
        silent = sv.verify(expr, on_inferred="silent")
    assert silent.proved
    assert "requires t: (_.qty != 0) (inferred from total // qty)" in str(silent)
    with pytest.raises(PreconditionError, match="inferred from `total // qty`"):
        silent.run(con)
    with pytest.raises(ValueError, match="on_inferred must be"):
        sv.verify(expr, on_inferred="never")  # type: ignore[arg-type]


def test_a_transform_raises_unless_told(con) -> None:
    src = StaticSource(pa.table({"id": [1], "amount": [3]}), name="orders")

    @sv.transform(requires={"orders": [_.amount >= 0]})
    def doubled(orders):
        return orders.select(orders.id, x=orders.amount * 2)

    with pytest.raises(
        VerificationError,
        match=r"needs: \(_.amount < 2\*\*62\) on orders, inferred from "
        r"`amount \* 2`",
    ):
        src.pipe(doubled)

    @sv.transform(requires={"orders": [_.amount >= 0]}, on_inferred="silent")
    def assumed(orders):
        return orders.select(orders.id, x=orders.amount * 2)

    node = src.pipe(assumed)
    assert node.refresh()["assumed"].route is not None

    @sv.transform(requires={"orders": [_.amount >= 0, _.amount < 2**62]})
    def stated(orders):
        return orders.select(orders.id, x=orders.amount * 2)

    src.pipe(stated).refresh()


def test_infer_false_still_turns_inference_off(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select(t.k, per=t.total // t.qty), on_inferred="off")
    assert report.inferred == {} and _needed(report) == {}
    assert any(i.kind == "division by zero" for i in report.errors)

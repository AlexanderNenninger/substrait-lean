"""The 0.6 API changes from the critique (#686): fewer knobs for "not
proved" (#690) and one name per concept (#695). Each renamed or removed
keyword keeps working for one release, with a `DeprecationWarning` that
names the replacement; the names deprecated before 0.5 are gone."""

import json
import warnings

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from _pipelines import doubled, make_orders, paid
from sverify import routes
from sverify.contracts import InferredPreconditionWarning
from sverify.engines import SNOWFLAKE, to_sql
from sverify.errors import (
    RouteError,
    UnverifiedRunError,
    UnverifiedRunWarning,
    VerificationError,
)
from sverify.io import DeltaSink, StaticSource

T = ibis.table({"k": "int64", "amount": "int64"}, name="t")
SUM = T.group_by("k").aggregate(total=T.amount.sum())


def _quiet(fn, *args, **kwargs):
    with warnings.catch_warnings():
        warnings.simplefilter("error", DeprecationWarning)
        return fn(*args, **kwargs)


@pytest.fixture
def con():
    c = sv.connect()
    c.put("t", pa.table({"k": [1, 1, 2], "amount": [3, 4, 5]}))
    return c


# -- #690: on_inferred="off" replaces infer=False -----------------------------


def test_on_inferred_off_infers_and_assumes_nothing() -> None:
    off = _quiet(sv.verify, SUM, on_inferred="off")
    assert not off.assumed and not off.inferred
    assert "SUM overflow" in [i.kind for i in off.errors]
    assert not off.proved
    # The other values assume the SUM fits, and check it at run time.
    assumed = _quiet(sv.verify, SUM)
    assert [i.kind for i in assumed.assumed] == ["SUM overflow"]


def test_verify_infer_false_is_deprecated_for_on_inferred_off() -> None:
    with pytest.warns(
        DeprecationWarning, match=r'verify\(infer=False\) is deprecated; write on_inferred="off"'
    ):
        old = sv.verify(SUM, infer=False)
    new = _quiet(sv.verify, SUM, on_inferred="off")
    assert old.issues == new.issues and old.assumed == new.assumed == []
    with pytest.warns(DeprecationWarning, match=r"verify\(infer=True\) is deprecated"):
        sv.verify(SUM, infer=True)


def test_transform_infer_false_is_deprecated_for_on_inferred_off() -> None:
    def f(t):
        return t

    with pytest.warns(
        DeprecationWarning, match=r'transform\(infer=False\) is deprecated; write on_inferred="off"'
    ):
        old = sv.transform(infer=False)(f)
    assert old.on_inferred == "off" and old.infer is False
    new = _quiet(sv.transform(on_inferred="off"), f)
    assert new.on_inferred == "off" and new.infer is False
    assert _quiet(sv.transform(), f).infer is True


def test_on_inferred_names_its_four_values() -> None:
    with pytest.raises(ValueError, match="'error', 'warn', 'silent' or 'off'"):
        sv.verify(SUM, on_inferred="never")  # type: ignore[arg-type]


def test_strict_is_removed() -> None:
    with pytest.raises(TypeError, match="strict"):
        sv.transform(strict=True)  # type: ignore[call-arg]


def test_an_assumed_sum_says_it_is_checked_at_run_time() -> None:
    report = _quiet(sv.verify, SUM)
    text = str(report)
    assert "SUM of amount fits 64 bits in every group (checked at run time" in text
    assert "(inferred;" not in text


def test_an_assumed_double_sum_names_the_sum() -> None:
    """The comment on #690: `temp_c may overflow to ±inf` named the column
    where its `SUM` overflows, when a `mean` read it too."""
    r = ibis.table({"k": "int64", "temp_c": "float64"}, name="readings")
    both = r.group_by("k").aggregate(s=r.temp_c.sum(), m=r.temp_c.mean(), hi=r.temp_c.max())
    report = _quiet(sv.verify, both, on_inferred="silent")
    assert "assumes: sum(temp_c) or mean(temp_c) stays finite" in str(report)


# -- #690: an unproved run raises a VerificationError -------------------------


def test_an_unproved_run_raises_unverified_run_error(con) -> None:
    report = _quiet(sv.verify, con.table("t").select("k", x=_.amount * _.amount), on_inferred="off")
    assert not report.proved
    with pytest.raises(
        UnverifiedRunError, match=r"run\(\.\.\., unverified=True\) runs it anyway"
    ) as e:
        report.run(con)
    assert isinstance(e.value, VerificationError) and isinstance(e.value, RouteError)
    assert e.value.report is report and e.value.route.refused


@sv.transform(ensures=[_.big > 100], on_unproved="warn")
def clipped(orders):
    return orders.select("id", big=orders.amount.clip(0, 10))


def test_on_unproved_warn_refreshes_unverified(tmp_path) -> None:
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    with pytest.warns(UserWarning):
        node = clipped(orders)
    with pytest.warns(UnverifiedRunWarning, match=r"unverified \(on_unproved='warn'\)"):
        out = node.refresh()
    assert out["clipped"].route is not None and out["clipped"].route.kind == "unverified"
    assert node.to_arrow().to_pylist() == [{"id": 1, "big": 5}]


@sv.transform(on_unproved="runtime")
def total(t):
    return t.group_by("k").aggregate(s=t.x.sum())


def test_an_unproved_refresh_raises_unverified_run_error() -> None:
    """A runtime error cannot be checked on the output data, so a
    `"runtime"` node that may raise one is not verified."""
    src = StaticSource(pa.table({"k": [1], "x": [1.5]}), name="t")
    node = total(src)
    with pytest.raises(UnverifiedRunError, match=r"refresh\(unverified=True\)") as e:
        node.refresh()
    assert isinstance(e.value, VerificationError) and isinstance(e.value, RouteError)
    with pytest.warns(UnverifiedRunWarning):
        node.refresh(unverified=True)


# -- #695: names ----------------------------------------------------------------


def test_the_route_reference_is_now_translated(con, tmp_path) -> None:
    report = _quiet(sv.verify, con.table("t").select("k"))
    assert _quiet(routes.choose, report, "duckdb").kind == "translated"
    with pytest.warns(
        DeprecationWarning, match=r'route="reference" is deprecated; write route="translated"'
    ):
        report.run(con, route="reference")
    assert report.routes["duckdb"].kind == "translated"
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    with pytest.warns(DeprecationWarning, match='route="translated"'):
        out = doubled(paid(orders)).refresh(route="reference")
    assert out["doubled"].route is not None and out["doubled"].route.kind == "translated"


def test_a_route_names_translated_by_its_class_alone() -> None:
    shim = routes.Route("polars", "translated", "reference", "why", cls="shim", evidence="tested")
    assert str(shim) == "shim; evidence tested"
    exact = routes.Route("duckdb", "native", "duckdb", "why", cls="exact")
    assert str(exact) == "exact; native: why"
    assert str(routes.Route("duckdb", None, "duckdb", "why")) == "refused: why"


def test_printed_output_says_semantics_where_a_profile_is_meant(con) -> None:
    report = _quiet(sv.verify, con.table("t").select("k"))
    refused = _quiet(routes.choose, report, "duckdb", "native")
    assert 'not verified under semantics="duckdb"' in refused.reason
    assert "Profile." not in refused.reason


def test_transform_engine_is_check_engine() -> None:
    def f(t):
        return t

    with pytest.warns(
        DeprecationWarning, match=r"transform\(engine=\.\.\.\) is deprecated; write check_engine="
    ):
        old = sv.transform(engine="duckdb")(f)
    assert old.check_engine == "duckdb"
    assert _quiet(sv.transform(check_engine="duckdb"), f).check_engine == "duckdb"


def test_run_check_inputs_is_check_requires(con) -> None:
    report = _quiet(sv.verify, con.table("t").select("k"))
    _quiet(report.run, con, check_requires=False)
    with pytest.warns(
        DeprecationWarning, match=r"run\(check_inputs=\.\.\.\) is deprecated; write check_requires="
    ):
        report.run(con, check_inputs=False)


def test_to_sql_takes_deterministic_and_a_plan_string(tmp_path) -> None:
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    node = paid(orders)
    plan = _quiet(lambda: node.internal_plan)
    text = _quiet(to_sql, plan, SNOWFLAKE, deterministic=True)
    assert text == _quiet(to_sql, json.loads(plan), SNOWFLAKE, deterministic=True)
    with pytest.warns(
        DeprecationWarning, match=r"to_sql\(tie_free=\.\.\.\) is deprecated; write deterministic="
    ):
        assert to_sql(plan, SNOWFLAKE, tie_free=True) == text


def test_node_plan_is_internal_plan(tmp_path) -> None:
    node = paid(make_orders(tmp_path / "orders", [(1, "ada", 5)]))
    with pytest.warns(
        DeprecationWarning, match=r"Node\.plan is deprecated; read node\.internal_plan"
    ):
        assert node.plan == node.internal_plan


def test_verify_takes_the_query_positionally() -> None:
    with pytest.raises(TypeError):
        sv.verify(transform=SUM)  # type: ignore[call-arg]


def test_needed_text_is_a_property() -> None:
    expr = T.select(x=T.amount * 2)
    report = _quiet(sv.verify, expr)
    assert report.needed and report.needed_text
    assert "(_.amount < 2**62) on t, inferred from `amount * 2`" in report.needed_text[0]
    with pytest.warns(
        DeprecationWarning,
        match=r"needs_lines\(\) is deprecated; read the property report\.needed_text",
    ):
        assert report.needs_lines() == report.needed_text
    with pytest.warns(DeprecationWarning, match=r"needs_text\(\) is deprecated"):
        report.needs_text("t", report.needed["t"])


def test_equivalence_is_the_observation() -> None:
    report = _quiet(sv.verify, T.select("k"), ensures=[sv.equivalent(rows="sequence")])
    assert report.equivalence is report.observation
    assert report.equivalence.rows == "sequence"


def test_inferred_warn_still_warns() -> None:
    with pytest.warns(InferredPreconditionWarning):
        sv.verify(T.select(x=T.amount * 2), on_inferred="warn")


# -- #695: refresh reports -------------------------------------------------------


@sv.transform(requires={"orders": [_.amount >= 0, _.amount < 1_000]})
def daily_revenue(orders):
    return orders.group_by("customer").aggregate(revenue=orders.amount.sum())


def test_a_refresh_report_is_headed_by_transform_and_sink(tmp_path) -> None:
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    node = daily_revenue(orders).write(DeltaSink(str(tmp_path / "daily")))
    out = _quiet(node.refresh)
    assert str(out).startswith("daily_revenue → daily:")
    assert out["daily"].heading == "daily_revenue → daily"


def test_a_summary_says_changes_from(tmp_path) -> None:
    src = StaticSource(pa.table({"k": [1], "amount": [3]}), name="payments")

    @sv.transform(requires={"payments": [_.amount >= 0, _.amount < 1_000]})
    def keep(payments):
        return payments

    node = keep(src)
    node.refresh()
    src.apply(sv.Changes(inserts=pa.table({"k": [2], "amount": [4]})))
    line = node.refresh()["keep"].summary()
    assert line.startswith("keep: changes from payments v0→v1"), line
    assert "Δ" not in line


# -- removed --------------------------------------------------------------------


def test_references_takes_to_only() -> None:
    with pytest.raises(TypeError):
        sv.references("cust", "customers", "id")  # type: ignore[misc]


def test_connection_datafusion_is_removed() -> None:
    assert not hasattr(sv.connect(), "datafusion")

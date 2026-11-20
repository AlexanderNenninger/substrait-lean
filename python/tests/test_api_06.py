"""The 0.6 API changes from the critique (#686): fewer knobs for "not
proved" (#690) and one name per concept (#695). The old names warned for
one release; 1.0 removes them (the API review's section M)."""

import json
import warnings
from typing import Any

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from _pipelines import doubled, make_orders, paid
from sverify import routes
from sverify.engines import to_sql
from sverify.errors import (
    InferredWarning,
    RouteError,
    UnverifiedRunError,
    UnverifiedRunWarning,
    VerificationError,
)
from sverify.io import Changes, DeltaSink, StaticSource

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
    assert not off.assumed and not off._inferred
    assert "SUM overflow" in [i.kind for i in off.errors]
    assert off.verdict == sv.Verdict.UNPROVED
    # The other values assume the SUM fits, and check it at run time.
    assumed = _quiet(sv.verify, SUM)
    assert [i.kind for i in assumed.assumed] == ["SUM overflow"]


def test_infer_is_removed() -> None:
    with pytest.raises(TypeError, match="infer"):
        sv.verify(SUM, infer=False)  # type: ignore[call-arg]
    with pytest.raises(TypeError, match="infer"):
        sv.transform(infer=False)  # type: ignore[call-arg]
    assert not hasattr(_quiet(sv.transform(on_inferred="off"), lambda t: t), "infer")


def test_on_inferred_names_its_four_values() -> None:
    with pytest.raises(ValueError, match="'error', 'warn', 'ignore' or 'off'"):
        sv.verify(SUM, on_inferred="never")  # type: ignore[arg-type]


def test_strict_is_removed() -> None:
    with pytest.raises(TypeError, match="strict"):
        sv.transform(strict=True)  # type: ignore[call-arg]


def test_an_assumed_sum_says_it_is_checked_at_run_time() -> None:
    report = _quiet(sv.verify, SUM)
    text = report.details()
    assert "SUM of amount fits 64 bits in every group (checked at run time" in text
    assert "(inferred;" not in text
    # The first line says the proof holds under checks (#1484).
    assert report.verdict == sv.Verdict.PROVED_WITH_CHECKS
    assert text.splitlines()[0].startswith("proved with checks: 1 assumption")
    assert "**proved with checks: 1 assumption**" in report._repr_markdown_()


def test_an_assumed_double_sum_names_the_sum() -> None:
    """The comment on #690: `temp_c may overflow to ±inf` named the column
    where its `SUM` overflows, when a `mean` read it too."""
    r = ibis.table({"k": "int64", "temp_c": "float64"}, name="readings")
    both = r.group_by("k").aggregate(s=r.temp_c.sum(), m=r.temp_c.mean(), hi=r.temp_c.max())
    report = _quiet(sv.verify, both, on_inferred="ignore")
    assert "assumes: sum(temp_c) or mean(temp_c) stays finite" in report.details()


# -- #690: an unproved run raises a VerificationError -------------------------


def test_an_unproved_run_raises_unverified_run_error(con) -> None:
    report = _quiet(sv.verify, con.table("t").select("k", x=_.amount * _.amount), on_inferred="off")
    assert report.verdict == sv.Verdict.UNPROVED
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


@sv.transform(on_unproved="check")
def total(t):
    return t.group_by("k").aggregate(s=t.x.sum())


def test_an_unproved_refresh_raises_unverified_run_error() -> None:
    """A runtime error cannot be checked on the output data, so a
    `"check"` node that may raise one is not verified."""
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
    _quiet(report.run, con, route="translated")
    assert report.routes["duckdb"].kind == "translated"
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    out = _quiet(doubled(paid(orders)).refresh, route="translated")
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

    with pytest.raises(TypeError, match="engine"):
        sv.transform(engine="duckdb")  # type: ignore[call-arg]
    assert _quiet(sv.transform(check_engine="duckdb"), f).check_engine == "duckdb"


def test_run_check_inputs_is_check_requires(con) -> None:
    report = _quiet(sv.verify, con.table("t").select("k"))
    _quiet(report.run, con, check_requires=False)
    with pytest.raises(TypeError, match="check_inputs"):
        report.run(con, check_inputs=False)  # type: ignore[call-arg]


def test_to_sql_takes_deterministic_and_a_plan_string(tmp_path) -> None:
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    node = paid(orders)
    plan = _quiet(lambda: node.internal_plan)
    text = _quiet(to_sql, plan, "snowflake", deterministic=True)
    assert text == _quiet(to_sql, json.loads(plan), "snowflake", deterministic=True)
    with pytest.raises(TypeError, match="tie_free"):
        to_sql(plan, "snowflake", tie_free=True)  # type: ignore[call-arg]


def test_node_plan_is_internal_plan(tmp_path) -> None:
    node = paid(make_orders(tmp_path / "orders", [(1, "ada", 5)]))
    assert node.internal_plan
    assert not hasattr(node, "plan")


def test_verify_takes_the_query_positionally() -> None:
    with pytest.raises(TypeError):
        sv.verify(transform=SUM)  # type: ignore[call-arg]


def test_needed_text_is_a_field() -> None:
    expr = T.select(x=T.amount * 2)
    report = _quiet(sv.verify, expr)
    n = next(n for n in report.needs if "< 2**62" in n.label)
    assert "(_.amount < 2**62) on t, inferred from `amount * 2`" in n.text
    assert not hasattr(report, "needs_lines") and not hasattr(report, "needs_text")
    with pytest.warns(DeprecationWarning, match=r"Report.needed is deprecated"):
        assert report.needed == {"t": [m.label for m in report.needs]}
    with pytest.warns(DeprecationWarning, match=r"Report.needed_text is deprecated"):
        assert report.needed_text == report._needs_lines()
    with pytest.warns(DeprecationWarning, match=r"Report.needed_conditions is deprecated"):
        conds = report.needed_conditions
    assert [repr(c) for c in conds["t"]] == [repr(m.condition) for m in report.needs]


def test_equivalence_is_the_observation() -> None:
    report = _quiet(sv.verify, T.select("k"), ensures=[sv.equivalent(rows="sequence")])
    assert not hasattr(report, "observation") and not hasattr(report, "equivalence")
    assert report.lenses.rows == "sequence"


def test_inferred_warn_still_warns() -> None:
    with pytest.warns(InferredWarning) as w:
        report = sv.verify(T.select(x=T.amount * 2), on_inferred="warn")
    assert w[0].message.report is report  # type: ignore[union-attr]


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
    src.apply(Changes(inserts=pa.table({"k": [2], "amount": [4]})))
    line = node.refresh()["keep"].summary()
    assert line.startswith("keep: changes from payments v0→v1"), line
    assert "Δ" not in line


# -- removed --------------------------------------------------------------------


def test_references_takes_to_only() -> None:
    with pytest.raises(TypeError):
        sv.references("cust", "customers", "id")  # type: ignore[misc]


def test_connection_datafusion_is_removed() -> None:
    assert not hasattr(sv.connect(), "datafusion")


# -- #1540: run checks the data against the schema the plan was verified for ---

ENGINES = ["duckdb", "polars"]
NON_NULL = pa.schema([pa.field("a", pa.int64(), nullable=False), pa.field("g", pa.int64())])


def _con(engine: str, data: dict[str, pa.Table]) -> Any:
    c = sv.connect(engine)
    for name, table in data.items():
        c.put(name, table)
    return c


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize(
    "query",
    [
        "SELECT g, count(a) AS n, min(a) AS m FROM t GROUP BY g",
        "SELECT a AS y FROM t",
    ],
)
def test_run_refuses_a_null_in_a_non_null_column(engine: str, query: str) -> None:
    report = sv.verify(query, tables={"t": NON_NULL}, ensures=["TRUE"])
    data = pa.table({"a": pa.array([1, None], pa.int64()), "g": [1, 1]})
    with pytest.raises(sv.errors.PreconditionError, match=r"column 'a' holds 1 NULL"):
        report.run(_con(engine, {"t": data}), engine=engine)


@pytest.mark.parametrize("engine", ENGINES)
def test_run_refuses_a_null_in_an_ibis_non_null_column(engine: str) -> None:
    t = ibis.table({"a": "!int64"}, name="t")
    report = sv.verify(t.select(y=t.a + 0), ensures=[_.y.notnull()])
    with pytest.raises(sv.errors.PreconditionError, match=r"column 'a' holds 1 NULL"):
        report.run(
            _con(engine, {"t": pa.table({"a": pa.array([1, None], pa.int64())})}), engine=engine
        )


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize(
    "build",
    [
        lambda t: t.select(y=t.a // 1),
        lambda t: t.select(y=100 // t.a),
        lambda t: t.select(y=t.a),
    ],
)
def test_run_refuses_a_double_in_an_integer_column(engine: str, build) -> None:
    t = ibis.table({"a": "int64"}, name="t")
    report = sv.verify(build(t), requires=[_.a != 0])
    with pytest.raises(sv.errors.PreconditionError, match=r"column 'a' is double"):
        report.run(_con(engine, {"t": pa.table({"a": [0.4, 2.0]})}), engine=engine)


@pytest.mark.parametrize("engine", ENGINES)
def test_run_accepts_a_matching_table_with_narrower_integers_and_a_nullable_column(
    engine: str,
) -> None:
    t = ibis.table({"a": "int64", "b": "!int64"}, name="t")
    report = sv.verify(t.select(y=t.a, z=t.b))
    data = pa.table({"a": pa.array([1, None], pa.int32()), "b": pa.array([2, 3], pa.int16())})
    assert report.run(_con(engine, {"t": data}), engine=engine).to_pylist() == [
        {"y": 1, "z": 2},
        {"y": None, "z": 3},
    ]


@pytest.mark.parametrize("engine", ENGINES)
def test_run_refuses_an_integer_outside_its_declared_width(engine: str) -> None:
    """D46: a physical type wider than the declared one gets one range check,
    on the engine; the refusal names the column, the type and a value."""
    t = ibis.table({"a": "int32"}, name="t")
    report = sv.verify(t.select(y=t.a))
    wide = pa.table({"a": pa.array([1, 2**40], pa.int64())})
    with pytest.raises(
        sv.errors.PreconditionError, match=r"column .a. is declared int32.*1099511627776"
    ):
        report.run(_con(engine, {"t": wide}), engine=engine)
    ok = pa.table({"a": pa.array([1, 2**30], pa.int64())})
    assert len(report.run(_con(engine, {"t": ok}), engine=engine).to_pylist()) == 2


def test_run_checks_no_range_when_the_physical_type_fits(monkeypatch) -> None:
    from sverify import report as report_module

    t = ibis.table({"a": "int32"}, name="t")
    report = sv.verify(t.select(y=t.a))
    seen: list[object] = []
    real = report_module.violation_counts
    monkeypatch.setattr(
        report_module, "violation_counts", lambda *args: seen.append(args) or real(*args)
    )
    report.run(_con("duckdb", {"t": pa.table({"a": pa.array([1, 2], pa.int16())})}))
    assert seen == []


@pytest.mark.parametrize("engine", ENGINES)
def test_run_refuses_a_string_in_a_date_column(engine: str) -> None:
    t = ibis.table({"d": "date"}, name="t")
    report = sv.verify(t.select(y=t.d))
    with pytest.raises(sv.errors.PreconditionError, match=r"column 'd' is string"):
        report.run(_con(engine, {"t": pa.table({"d": ["2024-01-01"]})}), engine=engine)


def _int32_report() -> sv.Report:
    t = ibis.table({"a": "int32"}, name="t")
    return sv.verify(t.select(y=t.a))


@pytest.mark.parametrize("engine", ENGINES)
def test_run_checks_the_schema_without_check_requires(engine: str) -> None:
    wide = pa.table({"a": pa.array([1, 2**40], pa.int64())})
    with pytest.raises(sv.errors.PreconditionError, match=r"column .a. is declared int32"):
        _int32_report().run(_con(engine, {"t": wide}), engine=engine, check_requires=False)


def test_run_range_checks_a_resident_table() -> None:
    from sverify_duckdb import DuckDBStore

    con = sv.connect()
    con.put("t", DuckDBStore().keep_table(pa.table({"a": pa.array([1, 2**40], pa.int64())})))
    with pytest.raises(sv.errors.PreconditionError, match=r"column .a. is declared int32"):
        _int32_report().run(con)


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize(
    ("declared", "physical", "value"),
    [("int32", pa.uint32(), 2**31), ("int64", pa.uint64(), 2**63 + 5)],
)
def test_run_refuses_an_unsigned_integer_outside_the_declared_type(
    engine: str, declared: str, physical: pa.DataType, value: int
) -> None:
    t = ibis.table({"a": declared}, name="t")
    report = sv.verify(t.select(y=t.a))
    data = pa.table({"a": pa.array([1, value], physical)})
    with pytest.raises(sv.errors.SverifyError):  # the range's refusal or the reader's (#350)
        report.run(_con(engine, {"t": data}), engine=engine)


def test_run_checks_every_read_of_a_table() -> None:
    from sverify._run_schema import declared_columns

    plan = {
        "a": {
            "namedTable": {"names": ["t"]},
            "baseSchema": {
                "names": ["a"],
                "struct": {"types": [{"i64": {"nullability": "NULLABILITY_NULLABLE"}}]},
            },
        },
        "b": {
            "namedTable": {"names": ["t"]},
            "baseSchema": {
                "names": ["a"],
                "struct": {"types": [{"i32": {"nullability": "NULLABILITY_NULLABLE"}}]},
            },
        },
    }
    [schemas] = declared_columns(plan).values()
    assert [d.int_key for [d] in schemas] == ["i64", "i32"]


@pytest.mark.parametrize("engine", ENGINES)
def test_run_adds_at_the_edge_of_a_narrower_physical_width(engine: str) -> None:
    """Probe (Fable): `int16` held, `int64` declared: `a + a` at 32767."""
    t = ibis.table({"a": "int64"}, name="t")
    report = sv.verify(t.select(y=t.a + t.a), requires=[_.a < 2**40, _.a > -(2**40)])
    data = pa.table({"a": pa.array([32767], pa.int16())})
    assert report.run(_con(engine, {"t": data}), engine=engine).to_pylist() == [{"y": 65534}]


def test_run_counts_the_nulls_of_a_resident_table() -> None:
    from sverify_duckdb import DuckDBStore

    t = ibis.table({"a": "!int64"}, name="t")
    report = sv.verify(t.select(y=t.a))
    con = sv.connect()
    con.put("t", DuckDBStore().keep_table(pa.table({"a": pa.array([1, None], pa.int64())})))
    with pytest.raises(sv.errors.PreconditionError, match=r"column 'a' holds 1 NULL"):
        report.run(con)
    con.put("t", DuckDBStore().keep_table(pa.table({"a": pa.array([1, 2], pa.int64())})))
    assert len(report.run(con).to_pylist()) == 2


def test_run_checks_a_native_table_in_one_plan(monkeypatch) -> None:
    from sverify import report as report_module
    from sverify_duckdb import DuckDBStore

    t = ibis.table({"a": "!int32", "b": "!int32"}, name="t")
    report = sv.verify(t.select(y=t.a, z=t.b))
    con = sv.connect()
    con.put(
        "t",
        DuckDBStore().keep_table(
            pa.table({"a": pa.array([1], pa.int64()), "b": pa.array([2], pa.int64())})
        ),
    )
    calls: list[int] = []
    real = report_module.violation_counts
    monkeypatch.setattr(
        report_module,
        "violation_counts",
        lambda table, conds, *rest: calls.append(len(conds)) or real(table, conds, *rest),
    )
    report.run(con)
    assert calls[0] == 4  # two NULL counts and two ranges, in one call

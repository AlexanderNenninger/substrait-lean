"""Spark as a profile (#739): `Profile.spark.table` and its shims
(`SubstraitLean/EngineTables.lean`, `SparkShims.lean`), `semantics="spark"`,
the routes to Spark, and the settings and version a run checks.

Lean proves each shim against a model of Spark from its facts
(`characterization/spark/facts/`) and `Rel.spark_sound`: Spark under ANSI, as
`sverify.sql.spark` writes it, gives `Rel.eval`'s rows for a verified plan.
That Spark computes as the model says is the trusted part; the tests marked
`backend("spark")` run it on a local session, against Python's exact
arithmetic.
"""

from __future__ import annotations

import math
from collections.abc import Iterator

import ibis
import pyarrow as pa
import pytest
from deltalake import DeltaTable
from hypothesis import given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from _pipelines import make_orders, paid
from sverify import _engine_settings, routes
from sverify.routes import EngineSettingsError, EngineVersionError, EngineVersionWarning
from sverify.sql.spark import SPARK_CONF

MIN, MAX = -(2**63), 2**63 - 1
SCHEMA = ibis.schema({"k": "string", "i": "int64", "x": "float64"})


def _rows(spark: dict) -> dict:
    return {(r["group"], r["option"]): r for r in spark}


@pytest.fixture(scope="module")
def tables() -> dict:
    return routes._options_json()


@pytest.fixture(scope="module")
def report() -> sv.Report:
    """A group-by verified under Spark's profile."""
    con = sv.connect()
    con.create("t", SCHEMA, [])
    t = con.table("t")
    r = sv.verify(
        t.group_by("k").aggregate(s=t.i.sum(), m=t.x.max(), n=t.i.count()),
        requires={"t": [_.i.between(-(10**15), 10**15)]},
        ensures=[_.n >= 0],
        semantics="spark",
    )
    assert r.proved and r.semantics == "spark", str(r)
    return r


# -- the tables, without a JVM -------------------------------------------------------


def test_the_profile_is_the_checkers(tables: dict) -> None:
    prof = tables["profiles"]["spark"]
    assert prof["engine"] == "spark" and prof["versions"] == ["4.3.0"]
    assert routes.profiles()["spark"].versions == ("4.3.0",)
    rows = _rows(tables["choices"]["spark"])
    # Spark's own choices, from its facts.
    assert rows[(None, "null_order")]["choice"]["default"] == ["NULLS_FIRST"]
    assert rows[(None, "avg_int_result")]["choice"]["behaviours"] == ["FP64"]
    assert rows[(None, "sum_order")]["choice"]["behaviours"] == ["ANY"]
    # Each shim is proved in Lean.
    shims = {r["shim"]: r for r in rows.values() if r.get("shim")}
    assert set(shims) == {
        "int_sum_decimal",
        "int_avg_decimal",
        "Dialect.canon",
        "null_order",
        "sort on the keys",
    }
    for name in ("int_sum_decimal", "int_avg_decimal", "null_order"):
        assert shims[name]["evidence"] == "proved"
        assert shims[name]["theorem"] == f"Spark.{name}"
    assert rows[(None, "overflow")]["theorem"] == "Rel.spark_sound"


def test_semantics_spark_runs_natively_on_spark(report: sv.Report) -> None:
    route = routes.choose(report, "spark")
    assert (route.kind, route.cls) == ("native", "exact"), route
    # The proof holds under DuckDB's choices too, option by option.
    assert routes.choose(report, "duckdb").kind == "transfer"


def test_the_reference_reaches_spark_with_its_shims() -> None:
    con = sv.connect()
    con.create("t", SCHEMA, [])
    t = con.table("t")
    r = sv.verify(
        t.group_by("k").aggregate(s=t.i.sum(), m=t.x.max()),
        requires={"t": [_.i.between(-100, 100)]},
    )
    route = routes.choose(r, "spark")
    assert (route.kind, route.cls) == ("translated", "shim"), route
    assert any("int_sum_decimal" in s for s in route.shims)


def test_a_session_without_ansi_is_refused(report: sv.Report) -> None:
    values = dict(SPARK_CONF)
    assert _engine_settings.differences("spark", values) == []
    values["spark.sql.ansi.enabled"] = "false"
    with pytest.raises(EngineSettingsError, match="spark.sql.ansi.enabled.*spark.conf.set"):
        routes.check_settings("spark", values, report.depends)


def test_a_legacy_setting_refuses_only_the_plans_it_changes() -> None:
    values = {**SPARK_CONF, "spark.sql.legacy.statisticalAggregate": "true"}
    with pytest.warns(routes.EngineSettingsWarning, match="does not rely on it"):
        routes.check_settings("spark", values, [{"group": None, "option": "overflow"}])
    with pytest.raises(EngineSettingsError, match="statisticalAggregate"):
        routes.check_settings("spark", values, [{"group": "agg.var", "option": "stat_degenerate"}])


def test_another_spark_version() -> None:
    with pytest.warns(EngineVersionWarning):
        routes.check_version("spark", "4.2.0")
    with pytest.raises(EngineVersionError, match="probed at 4.3.0"):
        routes.check_version("spark", "3.5.4")


def test_semantics_is_checked() -> None:
    with pytest.raises(ValueError, match="'spark'"):
        sv.verify(ibis.table(SCHEMA, name="t"), semantics="sparkk")  # type: ignore[arg-type]


# -- on Spark ---------------------------------------------------------------------


@pytest.fixture(scope="module")
def spark() -> Iterator:
    from spark_session import session

    yield session()


@pytest.mark.backend("spark")
def test_native_run(spark, report: sv.Report) -> None:
    con = sv.connect()
    con.create(
        "t", SCHEMA, [("a", 1, 1.5), ("a", 4, -0.0), ("b", -7, None), ("b", 3, float("nan"))]
    )
    out = report.run(con, "spark")
    assert report.routes["spark"].kind == "native"
    got = {r["k"]: (r["s"], r["m"], r["n"]) for r in out.to_pylist()}
    # NaN is the greatest double (spark-nan-order).
    assert got.pop("b")[::2] == (-4, 2) and got == {"a": (5, 1.5, 2)}
    m = [r["m"] for r in out.to_pylist() if r["k"] == "b"][0]
    assert m is not None and math.isnan(m)


@pytest.mark.backend("spark")
@settings(max_examples=15, deadline=None)
@given(
    xs=st.lists(
        st.one_of(st.integers(MIN, MAX), st.sampled_from([MIN, MAX, -1, 0, 1])),
        min_size=1,
        max_size=12,
    )
)
def test_int_sum_decimal_is_the_exact_sum(spark, xs: list[int]) -> None:
    """The trusted part of `Spark.int_sum_decimal`: Spark's `DECIMAL(38,0)`
    `SUM` of 64-bit values is the exact total, in any order, where a `BIGINT`
    one raises on a partial sum (spark-sum-int)."""
    from sverify import spark_engine

    spark_engine.put_tables({"xs": pa.table({"x": pa.array(xs, pa.int64())})}, spark)
    total = spark.sql("SELECT SUM(CAST(x AS DECIMAL(38,0))) AS s FROM xs").collect()[0]["s"]
    assert int(total) == sum(xs)


@pytest.mark.backend("spark")
def test_refresh_on_spark(spark, tmp_path) -> None:
    @sv.transform(
        requires={"t": [_.amount >= 0, _.amount < 1_000_000_000]},
        ensures=[_.total >= 0],
        semantics="spark",
    )
    def totals(t):
        return t.group_by("customer").aggregate(total=t.amount.sum())

    orders = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "ada", 7), (3, "bob", 2)])
    node = totals(paid(orders)).write(sv.io.DeltaSink(str(tmp_path / "totals")))
    out = node.refresh(engine="spark")
    route = out["totals"].route
    assert route is not None and (route.kind, route.engine) == ("native", "spark")
    rows = DeltaTable(str(tmp_path / "totals")).to_pyarrow_table().to_pylist()
    assert sorted((r["customer"], r["total"]) for r in rows) == [("ada", 12), ("bob", 2)]

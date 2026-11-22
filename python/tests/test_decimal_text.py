"""Casts of decimals to VARCHAR (#346, D72): the scale's digits on every engine, a `DECIMAL(p, p)`
with its integer part (`0.500`; DuckDB's own cast prints `.500`), the refusals of the lift and of
`DECIMAL(38, 38)` on DuckDB, and of timestamps."""

from __future__ import annotations

from decimal import Decimal

import ibis
import pyarrow as pa
import pytest

import sverify as sv

SPARK = pytest.mark.backend("spark")
ENGINES = ["duckdb", "polars", pytest.param("spark", marks=SPARK)]

#: Column name: (precision, scale, values).
COLUMNS: dict[str, tuple[int, int, list[Decimal | None]]] = {
    "two": (10, 2, [Decimal("10.50"), Decimal("-0.05"), Decimal("0.00"), None, Decimal("-1234.5")]),
    "zero": (10, 0, [Decimal("12"), Decimal("-3"), Decimal("0"), None, Decimal("9999999999")]),
    # Tiny magnitudes: Spark prints plain digits, never `1E-7`.
    "tiny": (
        20,
        10,
        [Decimal("0.0000000001"), Decimal("-0.0000001"), Decimal("0"), None, Decimal("1")],
    ),
    # Precision equal to scale: DuckDB's own cast prints `.5`.
    "same3": (
        3,
        3,
        [Decimal("0.500"), Decimal("-0.500"), Decimal("0.000"), None, Decimal("0.001")],
    ),
    "same18": (
        18,
        18,
        [
            Decimal("0.5"),
            Decimal("-0.000000000000000001"),
            Decimal("0"),
            None,
            Decimal("0.999999999999999999"),
        ],
    ),
    "same37": (
        37,
        37,
        [
            Decimal("0.5"),
            Decimal("-0.5"),
            Decimal("0"),
            None,
            Decimal("0.0000000000000000000000000000000000001"),
        ],
    ),
    # The widest.
    "wide0": (
        38,
        0,
        [Decimal("9" * 38), Decimal("-" + "9" * 38), Decimal("0"), None, Decimal("1")],
    ),
    "wide10": (
        38,
        10,
        [
            Decimal("9" * 28 + "." + "9" * 10),
            Decimal("-0.0000000001"),
            Decimal("0"),
            None,
            Decimal("1"),
        ],
    ),
    "wide37": (
        38,
        37,
        [
            Decimal("0.5"),
            Decimal("-9.9999999999999999999999999999999999999"),
            Decimal("0"),
            None,
            Decimal("1"),
        ],
    ),
}


def _table(names) -> pa.Table:
    return pa.table(
        {n: pa.array(COLUMNS[n][2], pa.decimal128(COLUMNS[n][0], COLUMNS[n][1])) for n in names}
    )


def _want(name: str) -> list[str | None]:
    scale = COLUMNS[name][1]
    return [None if v is None else f"{v:.{scale}f}" for v in COLUMNS[name][2]]


def _ibis(names) -> ibis.Table:
    return ibis.table({n: f"decimal({COLUMNS[n][0]}, {COLUMNS[n][1]})" for n in names}, name="t")


def _run(report, engine, names):
    con = sv.connect("duckdb" if engine == "spark" else engine)
    con.put("t", _table(names))
    return report.run(con, engine, unverified=True)


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("name", [n for n in COLUMNS if n != "same37"])
def test_a_decimal_casts_to_its_text(engine, name):
    t = _ibis([name])
    report = sv.verify(t.select(x=t[name].cast("string")), counterexamples=0)
    assert _run(report, engine, [name]).column("x").to_pylist() == _want(name)


@pytest.mark.parametrize("engine", ENGINES)
def test_the_widest_precision_equal_to_scale_below_38_has_its_integer_part(engine):
    t = _ibis(["same37"])
    report = sv.verify(t.select(x=t.same37.cast("string")), counterexamples=0)
    assert _run(report, engine, ["same37"]).column("x").to_pylist() == _want("same37")


def test_a_decimal_38_38_is_refused_on_duckdb_in_the_report():
    t = ibis.table({"d": "decimal(38, 38)"}, name="t")
    report = sv.verify(t.select(x=t.d.cast("string")), counterexamples=0)
    route = report.route("duckdb")
    assert route.refused
    assert "DECIMAL(38, 38)" in route.why and "DECIMAL(38, 37)" in route.why


def test_a_decimal_38_37_is_not():
    t = ibis.table({"d": "decimal(38, 37)"}, name="t")
    report = sv.verify(t.select(x=t.d.cast("string")), counterexamples=0)
    assert not report.route("duckdb").refused


def test_the_lift_refuses_the_text_of_a_decimal_with_precision_equal_to_scale():
    t = _ibis(["same3", "two"])
    with pytest.raises(Exception, match=r"\.500.*0\.500|0\.500.*\.500") as e:
        sv.verify(sv.sql("SELECT CAST(same3 AS VARCHAR) AS x FROM t", dialect="duckdb", t=t))
    assert "DECIMAL(4, 3)" in str(e.value)


def test_the_lift_reads_the_text_of_any_other_decimal_as_duckdb_prints_it():
    t = _ibis(["two", "wide10"])
    sql = "SELECT CAST(two AS VARCHAR) AS a, CAST(wide10 AS VARCHAR) AS b FROM t"
    report = sv.verify(sv.sql(sql, dialect="duckdb", t=t), counterexamples=0)
    out = _run(report, "duckdb", ["two", "wide10"])
    assert out.column("a").to_pylist() == _want("two")
    assert out.column("b").to_pylist() == _want("wide10")


def test_a_constant_decimal_folds_to_its_text():
    t = _ibis(["two"])
    sql = "SELECT CAST(CAST('-0.05' AS DECIMAL(10, 2)) AS VARCHAR) AS a FROM t"
    out = _run(sv.verify(sv.sql(sql, dialect="duckdb", t=t), counterexamples=0), "duckdb", ["two"])
    assert out.column("a")[0].as_py() == "-0.05"


def test_a_timestamp_stays_refused_and_names_strftime():
    t = ibis.table({"ts": "timestamp"}, name="t")
    with pytest.raises(Exception, match="strftime") as e:
        sv.verify(t.select(x=t.ts.cast("string")), counterexamples=0)
    assert "%Y-%m-%d %H:%M:%S" in str(e.value)

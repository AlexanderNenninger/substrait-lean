"""`%` of decimals (D62, #1941): the truncated remainder of the two values at the
larger scale, with the dividend's sign, of type `DECIMAL(min(p₁ − s₁, p₂ − s₂) + s, s)`.
DuckDB gives it in a wider type, which the translation casts; Polars's remainder takes
the divisor's sign, which a shim takes off (`*-decimal-modulus` facts)."""

from decimal import Decimal as D

import ibis
import pyarrow as pa
import pytest

import sverify as sv

A = [D("7.50"), D("-7.50"), D("7.50"), D("-7.50"), None, D("1234.56"), D("-0.30")]
B = [D("2.0"), D("2.0"), D("-2.0"), D("-2.0"), D("1.0"), D("3.7"), D("0.7")]
#: Python's `Decimal` `%` is the truncated remainder, the dividend's sign.
TRUNCATED = [None if a is None else a % b for a, b in zip(A, B, strict=True)]
#: Polars's own: the divisor's sign.
FLOORED = [None if a is None else a - b * (a / b).to_integral_value("ROUND_FLOOR")
           for a, b in zip(A, B, strict=True)]  # fmt: skip
NONZERO = {"t": ['"b" IS NULL OR "b" <> 0']}

t = ibis.table({"a": "decimal(10, 2)", "b": "decimal(5, 1)", "n": "int64"}, name="t")


def con_with():
    con = sv.connect()
    con.put(
        "t",
        pa.table(
            {
                "a": pa.array(A, pa.decimal128(10, 2)),
                "b": pa.array(B, pa.decimal128(5, 1)),
                "n": pa.array([3, 3, -3, -3, 1, 7, 1], pa.int64()),
            }
        ),
    )
    return con


def run(report, engine: str) -> pa.Table:
    if engine == "spark":
        pytest.importorskip("pyspark")
    return report.run(con_with(), engine)


@pytest.mark.parametrize("engine", ["duckdb", "polars", "spark"])
def test_a_decimal_remainder_takes_the_dividends_sign(engine) -> None:
    report = sv.verify(t.select(r=t.a % t.b), requires=NONZERO)
    assert report.verdict == sv.Verdict.PROVED, str(report)
    out = run(report, engine)
    assert out.schema.field("r").type == pa.decimal128(6, 2)
    assert out.column("r").to_pylist() == TRUNCATED


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_decimal_remainder_by_an_integer(engine) -> None:
    """An integer is the `DECIMAL(19, 0)` it widens to."""
    report = sv.verify(t.select(r=t.a % t.n))
    assert report.verdict == sv.Verdict.PROVED, str(report)
    got = run(report, engine).column("r").to_pylist()
    ns = [3, 3, -3, -3, 1, 7, 1]
    assert got == [None if a is None else a % n for a, n in zip(A, ns, strict=True)]


def test_a_zero_divisor_is_an_error() -> None:
    assert "division by zero" in [i.kind for i in sv.verify(t.select(r=t.a % (t.b - t.b))).errors]


def test_past_38_digits_at_the_larger_scale_is_refused() -> None:
    """DuckDB computes a DOUBLE there (ruling 188): the message names the cast."""
    w = ibis.table({"a": "decimal(38, 10)", "b": "decimal(38, 0)"}, name="w")
    with pytest.raises(Exception, match="cast an operand to a DECIMAL with fewer digits"):
        sv.verify(w.select(r=w.a % w.b))


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_duckdb_sql_reads_decimal_modulus_in_duckdbs_type(engine) -> None:
    """The lift widens the remainder to DuckDB's type, the operands' common
    decimal (duckdb-decimal-modulus)."""
    report = sv.verify("SELECT a % b AS r FROM t", tables={"t": t.schema()}, requires=NONZERO)
    assert report.verdict == sv.Verdict.PROVED, str(report)
    out = run(report, engine)
    assert out.schema.field("r").type == pa.decimal128(10, 2)
    assert out.column("r").to_pylist() == TRUNCATED


def test_duckdb_sql_past_38_digits_is_refused() -> None:
    w = ibis.table({"a": "decimal(38, 9)", "b": "decimal(10, 10)"}, name="w")
    with pytest.raises(Exception, match="cast an operand to a DECIMAL with fewer digits"):
        sv.verify("SELECT a % b AS r FROM w", tables={"w": w.schema()})


def test_polars_semantics_floors() -> None:
    """Under `semantics="polars"` the remainder is Polars's own (`Profile.polars`)."""
    report = sv.verify(t.select(r=t.a % t.b), semantics="polars", requires=NONZERO)
    assert report.verdict == sv.Verdict.PROVED, str(report)
    assert run(report, "polars").column("r").to_pylist() == FLOORED

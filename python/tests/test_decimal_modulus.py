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
#: The analysis rules a zero divisor out from a bound on the divisor's column, not from `b <> 0`
#: (the unscaled divisor is `b * 10`): one run per sign of the divisor, with its rows.
ROWS = {"pos": [0, 1, 4, 5, 6], "neg": [2, 3]}
REQ_B = {"pos": ['"b" >= 0.1'], "neg": ['"b" <= -0.1']}
#: Bounded both ways, so the remainder (smaller than the divisor) fits the type.
REQ_N = {"pos": ['"n" >= 1', '"n" <= 10'], "neg": ['"n" <= -1', '"n" >= -10']}
NS = [3, 3, -3, -3, 1, 7, 1]
SIGNS = pytest.mark.parametrize("sign", ["pos", "neg"])

t = ibis.table({"a": "decimal(10, 2)", "b": "decimal(5, 1)", "n": "int64"}, name="t")


def pick(values: list, sign: str) -> list:
    return [values[i] for i in ROWS[sign]]


def con_with(sign: str):
    con = sv.connect()
    con.put(
        "t",
        pa.table(
            {
                "a": pa.array(pick(A, sign), pa.decimal128(10, 2)),
                "b": pa.array(pick(B, sign), pa.decimal128(5, 1)),
                "n": pa.array(pick(NS, sign), pa.int64()),
            }
        ),
    )
    return con


def run(report, engine: str, sign: str) -> pa.Table:
    if engine == "spark":
        pytest.importorskip("pyspark")
    return report.run(con_with(sign), engine)


@SIGNS
@pytest.mark.parametrize("engine", ["duckdb", "polars", "spark"])
def test_a_decimal_remainder_takes_the_dividends_sign(engine, sign) -> None:
    report = sv.verify(t.select(r=t.a % t.b), requires={"t": REQ_B[sign]})
    assert report.verdict == sv.Verdict.PROVED, str(report)
    out = run(report, engine, sign)
    assert out.schema.field("r").type == pa.decimal128(6, 2)
    assert out.column("r").to_pylist() == pick(TRUNCATED, sign)


@SIGNS
@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_decimal_remainder_by_an_integer(engine, sign) -> None:
    """An integer is the `DECIMAL(19, 0)` it widens to."""
    report = sv.verify(t.select(r=t.a % t.n), requires={"t": REQ_N[sign]})
    assert report.verdict == sv.Verdict.PROVED, str(report)
    got = run(report, engine, sign).column("r").to_pylist()
    assert got == [
        None if a is None else a % n for a, n in zip(pick(A, sign), pick(NS, sign), strict=True)
    ]


def test_a_zero_divisor_is_an_error() -> None:
    assert "division by zero" in [i.kind for i in sv.verify(t.select(r=t.a % (t.b - t.b))).errors]


def test_past_38_digits_at_the_larger_scale_is_refused() -> None:
    """DuckDB computes a DOUBLE there (ruling 188): the message names the cast."""
    w = ibis.table({"a": "decimal(38, 10)", "b": "decimal(38, 0)"}, name="w")
    with pytest.raises(Exception, match="cast an operand to a DECIMAL with fewer digits"):
        sv.verify(w.select(r=w.a % w.b))


@SIGNS
@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_duckdb_sql_reads_decimal_modulus_in_duckdbs_type(engine, sign) -> None:
    """The lift widens the remainder to DuckDB's type, the operands' common
    decimal (duckdb-decimal-modulus)."""
    report = sv.verify(
        "SELECT a % b AS r FROM t", tables={"t": t.schema()}, requires={"t": REQ_B[sign]}
    )
    assert report.verdict == sv.Verdict.PROVED, str(report)
    out = run(report, engine, sign)
    assert out.schema.field("r").type == pa.decimal128(10, 2)
    assert out.column("r").to_pylist() == pick(TRUNCATED, sign)


def test_duckdb_sql_past_38_digits_is_refused() -> None:
    w = ibis.table({"a": "decimal(38, 9)", "b": "decimal(10, 10)"}, name="w")
    with pytest.raises(Exception, match="cast an operand to a DECIMAL with fewer digits"):
        sv.verify("SELECT a % b AS r FROM w", tables={"w": w.schema()})


@SIGNS
def test_polars_semantics_floors(sign) -> None:
    """Under `semantics="polars"` the remainder is Polars's own (`Profile.polars`)."""
    report = sv.verify(t.select(r=t.a % t.b), semantics="polars", requires={"t": REQ_B[sign]})
    assert report.verdict == sv.Verdict.PROVED, str(report)
    assert run(report, "polars", sign).column("r").to_pylist() == pick(FLOORED, sign)

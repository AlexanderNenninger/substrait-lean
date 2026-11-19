"""`Report.output` types a decimal column as the checker does, which is the type
a run returns (#1484): Ibis's `AVG` and `SUM` of a decimal differ from the
reference's (`docs/reference-semantics.md`, Decimals)."""

import decimal

import ibis
import ibis.expr.datatypes as dt
import pyarrow as pa
import pytest

import sverify as sv

ENGINES = ["duckdb", "polars"]


def ibis_type(arrow: pa.DataType):
    return dt.dtype(ibis.formats.pyarrow.PyArrowType.to_ibis(arrow))


def table():
    return ibis.table({"h": "string", "a": "decimal(10, 2)", "i": "int32", "j": "int64"}, name="t")


def data():
    return pa.table(
        {
            "h": ["a", "a"],
            "a": pa.array([decimal.Decimal("1.50"), decimal.Decimal("2.25")], pa.decimal128(10, 2)),
            "i": pa.array([1, 2], pa.int32()),
            "j": [1, 2],
        }
    )


def run_types(report, tbl, engine, **kw):
    con = sv.connect()
    con.put("t", tbl)
    return {f.name: ibis_type(f.type) for f in report.run(con, engine, **kw).schema}


CASES3 = {
    "decimal AVG": lambda t: t.group_by("h").aggregate(m=t.a.mean()),
    "integer mean": lambda t: t.group_by("h").aggregate(m=t.i.mean(), n=t.j.mean()),
    "decimal SUM": lambda t: t.group_by("h").aggregate(s=t.a.sum()),
}


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("name", CASES3)
def test_output_equals_the_types_a_run_returns(name, engine):
    t = table()
    report = sv.verify(CASES3[name](t))
    try:
        got = run_types(report, data(), engine, unverified=True)
    except Exception as e:  # noqa: BLE001 - a plan an engine does not run (#271)
        if engine == "polars" and "Unsupported" in type(e).__name__:
            pytest.skip(str(e))
        raise
    assert dict(report.output) == got


def test_the_report_states_the_reference_decimal_types():
    t = table()
    report = sv.verify(t.group_by("h").aggregate(m=t.a.mean(), s=t.a.sum()))
    # AVG is DECIMAL(p + 4, s + 4), SUM DECIMAL(min(38, p + 10), s); Ibis says (10, 2) and (38, 2).
    assert report.output["m"] == dt.Decimal(14, 6)
    assert report.output["s"] == dt.Decimal(20, 2)


@pytest.mark.parametrize("name", ["decimal AVG", "decimal SUM"])
def test_output_equals_the_run_under_the_duckdb_profile(name):
    t = table()
    report = sv.verify(CASES3[name](t), semantics="duckdb")
    assert dict(report.output) == run_types(report, data(), "duckdb")


def dtable(p, s):
    return ibis.table(
        {"h": "string", "a": f"decimal({p}, {s})", "b": f"decimal({p}, {s})"}, name="t"
    )


#: The coverage cases have no decimal column, so the sweep is its own: every
#: decimal aggregate and arithmetic over several widths.
SWEEP = {
    "sum": lambda t: t.group_by("h").aggregate(x=t.a.sum()),
    "avg": lambda t: t.group_by("h").aggregate(x=t.a.mean()),
    "sum and avg, no keys": lambda t: t.aggregate(x=t.a.sum(), y=t.a.mean()),
    "min and max": lambda t: t.group_by("h").aggregate(x=t.a.min(), y=t.a.max()),
    "sum where": lambda t: t.group_by("h").aggregate(x=t.a.sum(where=t.b > 0)),
    "count and sum": lambda t: t.group_by("h").aggregate(n=t.a.count(), x=t.a.sum()),
    "passthrough": lambda t: t.select("h", "a"),
    "sum of a sum": lambda t: t.group_by("h").aggregate(x=t.a.sum()).aggregate(y=ibis._.x.sum()),
}


@pytest.mark.parametrize("pq", [(10, 2), (18, 0), (20, 6), (30, 4)])
@pytest.mark.parametrize("name", SWEEP)
def test_output_decimals_equal_the_run_on_a_sweep_of_decimal_aggregates(name, pq):
    """Run on empty tables: each decimal output column has the type the run
    returns on DuckDB."""
    t = dtable(*pq)
    report = sv.verify(SWEEP[name](t))
    con = sv.connect()
    con.put("t", t.schema().to_pyarrow().empty_table())
    got = report.run(con, "duckdb", unverified=True).schema
    for f in got:
        want = report.output[f.name]
        if want.is_decimal():
            assert want == ibis_type(f.type), f.name

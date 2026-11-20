"""Decimal `+` and `-` across scales: DuckDB casts each operand to the result
type and raises there, also where the exact sum fits
(`duckdb-decimal-addsub-operand-cast`, #1484). The model checks the result
only, so a cancelling sum, an operand at or above `10^(38 - s)` with the other
bringing the result back under 38 digits, is the case where the two differ.
Operands that do not cancel raise in both."""

import json

import duckdb
import ibis
import pyarrow as pa
import pytest

from sverify.sql_lift import lift
from sverify.testing import LeanRaised, lean_values
from sverify_dev import slt
from sverify_dev.lift import duckdb_result

pytestmark = pytest.mark.backend("duckdb")

#: (type of a, a, type of b, b, operation)
CASES = [
    pytest.param(
        ("DECIMAL(38,0)", "10000000000000000000000000000"),
        ("DECIMAL(38,10)", "-0.0000000001"),
        "+",
        id="d38_0-plus-d38_10-cancels",
    ),
    pytest.param(
        ("DECIMAL(38,0)", "10000000000000000000000000000"),
        ("DECIMAL(38,10)", "0.0000000001"),
        "-",
        id="d38_0-minus-d38_10-cancels",
    ),
    pytest.param(
        ("BIGINT", "100000000"),
        ("DECIMAL(38,30)", "-0.000000000000000000000000000001"),
        "+",
        id="bigint-plus-d38_30-cancels",
    ),
    # Large operands that do not cancel raise in both.
    pytest.param(
        ("DECIMAL(38,0)", "10000000000000000000000000000"),
        ("DECIMAL(38,10)", "1.5"),
        "+",
        id="d38_0-plus-d38_10-overflows",
    ),
    pytest.param(
        ("BIGINT", "9007199254740993"),
        ("DECIMAL(38,30)", "1.5"),
        "+",
        id="bigint-plus-d38_30-overflows",
    ),
    # Operands that fit the result type agree.
    pytest.param(
        ("DECIMAL(38,0)", "1000000000000000000000000000"),
        ("DECIMAL(38,10)", "1.5"),
        "+",
        id="d38_0-plus-d38_10-fits",
    ),
    pytest.param(
        ("DECIMAL(30,0)", "1000000000000000000000000001"),
        ("DECIMAL(38,10)", "-1.5"),
        "+",
        id="d30_0-plus-d38_10-fits",
    ),
]


def _table(a: tuple[str, str], b: tuple[str, str]) -> pa.Table:
    con = duckdb.connect()
    return con.sql(f"SELECT {a[1]}::{a[0]} AS a, {b[1]}::{b[0]} AS b").to_arrow_table()


@pytest.mark.parametrize(("a", "b", "op"), CASES)
def test_decimal_sum_raises_where_duckdb_does(a, b, op):
    table = _table(a, b)
    query = f"SELECT a {op} b AS x FROM t"
    try:
        expected: list | None = duckdb_result(query, {"t": table}).column("x").to_pylist()
    except duckdb.Error:
        expected = None
    plan = lift(query, {"t": ibis.Schema.from_pyarrow(table.schema)}).plan
    rows = {"t": [tuple(r.values()) for r in table.to_pylist()]}
    try:
        got: list | None = [
            r[0] for r in lean_values(json.dumps(slt._typed_inline(plan, rows, None)))
        ]
    except LeanRaised:
        got = None
    assert got == expected

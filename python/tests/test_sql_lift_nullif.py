"""`NULLIF(a, b)` in the lift: DuckDB compares in the common type and returns
`a` itself, at `a`'s type (`duckdb-nullif-type`, #1484)."""

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

_DUCK_TYPES = {"int8": "TINYINT", "int32": "INTEGER", "int64": "BIGINT", "float64": "DOUBLE"}
TABLE = pa.table(
    {
        "i8": pa.array([1, 100], pa.int8()),
        "i32": pa.array([1, 2], pa.int32()),
        "i64": pa.array([9007199254740993, 5], pa.int64()),
        "f64": pa.array([9007199254740992.0, 2.0], pa.float64()),
    }
)
SCHEMAS = {"t": ibis.Schema.from_pyarrow(TABLE.schema)}


def _duckdb_typeof(query: str) -> str:
    con = duckdb.connect()
    con.register("t", TABLE)
    return str(con.execute(f"SELECT typeof(x) FROM ({query}) s LIMIT 1").fetchall()[0][0])


@pytest.mark.parametrize(
    "expr",
    ["NULLIF(i32, f64)", "NULLIF(i32, i64)", "NULLIF(i64, i32)", "NULLIF(i8, 100)",
     "NULLIF(100, i8)", "NULLIF(f64, i32)", "NULLIF(i32, i32)"],
)  # fmt: skip
def test_nullif_has_the_type_of_its_first_argument(expr):
    query = f"SELECT {expr} AS x FROM t"
    assert _DUCK_TYPES[str(lift(query, SCHEMAS).schema["x"])] == _duckdb_typeof(query)


@pytest.mark.parametrize(
    "expr",
    [
        # BIGINT 2^53 + 1 against the double 2^53: equal as doubles, so NULL.
        "NULLIF(i64, f64)",
        "NULLIF(i32, f64)",
        "NULLIF(i32, i64)",
        "NULLIF(i64, i32)",
        # A sum at the INTEGER's width raises as DuckDB's does; cast through
        # the common type it would be a double sum.
        "NULLIF(i32, f64) + 2147483647",
        "NULLIF(i32, f64) + 9223372036854775807",
    ],
)
def test_nullif_returns_the_value_or_raises_as_duckdb_does(expr):
    query = f"SELECT {expr} AS x FROM t"
    try:
        expected: list | None = duckdb_result(query, {"t": TABLE}).column("x").to_pylist()
    except duckdb.Error:
        expected = None
    plan = lift(query, SCHEMAS).plan
    rows = {"t": [tuple(r.values()) for r in TABLE.to_pylist()]}
    try:
        got: list | None = [r[0] for r in lean_values(_inline(plan, rows))]
    except LeanRaised:
        got = None
    assert got == expected, query


def _inline(plan: dict, rows: dict) -> str:
    return json.dumps(slt._typed_inline(plan, rows, None))

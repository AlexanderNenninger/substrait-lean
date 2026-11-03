"""Casts in DuckDB SQL through sverify's own lift (`sverify.sql_lift`):
oracles A and C, the semantics' casts, and the refusals."""

import json

import ibis
import pytest

from _sql_lift import SCHEMAS, TABLES
from sverify.engine import run_checker
from sverify.plan_json import Unsupported as Refused
from sverify.sql_lift import lift
from sverify_dev.lift import check

pytestmark = pytest.mark.backend("duckdb")

#: Queries of the subset, each through oracles A and C.
QUERIES = [
    "SELECT id, CAST(qty AS DOUBLE) / 4 AS x, CAST(amount AS INTEGER) AS i,"
    " CAST(qty AS BIGINT) AS b FROM orders",
]


@pytest.mark.parametrize("query", QUERIES)
def test_oracles_a_and_c(query):
    # A: DuckDB on the SQL, and Lean on the lifted plan. C: DuckDB on the
    # plan Lean writes back.
    result = check(query, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


@pytest.mark.parametrize("query", [q for q in QUERIES if isinstance(q, str)])
def test_the_reference_lift_is_checked_too(query):
    plan = json.dumps(lift(query, SCHEMAS, "reference").plan)
    code, out, err = run_checker((), plan)
    assert code == 0, err or out


def test_a_double_cast_to_an_integer_depends_on_the_semantics():
    query = "SELECT CAST(price AS INTEGER) AS i FROM orders"
    with pytest.raises(Refused, match="TIE_TO_EVEN"):
        lift(query, SCHEMAS, "duckdb")
    # The reference truncates (#209 R9), which the plan's cast means.
    assert lift(query, SCHEMAS, "reference").schema == ibis.schema({"i": "int32"})


@pytest.mark.parametrize(
    ("query", "message"),
    [
        ("SELECT '1e38'::DECIMAL(38,0)", "does not fit"),
        ('SELECT 42::TINYINT::"null"', "CAST to"),
        ("SELECT TRY_CAST(id AS INT) FROM orders", "TRY_CAST"),
        ("SELECT CAST(price AS HUGEINT) FROM orders", "HUGEINT"),
        ("SELECT CAST(NULL AS INT[3]) FROM orders", "fixed-size array"),
    ],
)
def test_refusals_say_what(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, SCHEMAS)


def test_constants_out_of_range_are_cast_not_folded():
    # `200::TINYINT` raises in DuckDB: the plan casts, it doesn't hold an
    # INT8 literal of 200.
    plan = lift("SELECT 200::TINYINT AS x, 100::TINYINT AS y", {}).plan
    exprs = plan["relations"][0]["root"]["input"]["project"]["expressions"]
    assert "cast" in exprs[0] and exprs[1] == {"literal": {"i8": 100}}


def test_a_string_read_as_a_decimal_rounds_as_duckdb():
    # Half away from zero past the scale; DuckDB raises only where the
    # rounded value does not fit.
    query = (
        "SELECT '1.5'::DECIMAL(2,0) AS a, '-2.5'::DECIMAL(2,0) AS b,"
        " '1.25'::DECIMAL(3,1) AS c, '9.4'::DECIMAL(1,0) AS d"
    )
    result = check(query, {})
    assert result.ok, f"{result.stage}: {result.detail}"
    with pytest.raises(Refused, match="does not fit"):
        lift("SELECT '9.99'::DECIMAL(1,0)", {})

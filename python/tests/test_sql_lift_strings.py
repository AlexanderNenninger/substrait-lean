"""Strings in DuckDB SQL through sverify's own lift (`sverify.sql_lift`):
oracles A and C, and the refusals."""

import json

import pytest

from _sql_lift import SCHEMAS, TABLES
from sverify.engine import run_checker
from sverify.plan_json import Unsupported as Refused
from sverify.sql_lift import lift
from sverify_dev.lift import check

pytestmark = pytest.mark.backend("duckdb")

#: Queries of the subset, each through oracles A and C.
QUERIES = [
    # Strings: DuckDB counts characters (code points) from 1; LIKE has no
    # escape character; `||` is NULL with a NULL, `concat` leaves NULLs out.
    "SELECT id, length(customer) AS l, substring(customer, 2, 2) AS a,"
    " substring(customer, -2, 2) AS b, substring(customer, 0, 2) AS c, substr(customer, 2) AS d"
    " FROM orders",
    # The ends of the offsets and lengths DuckDB takes (#336).
    "SELECT substring(customer, 4294967295, 2) AS a, substring(customer, -4294967296, 4294967295)"
    " AS b, substring(customer, 1, 4294967295) AS c FROM orders",
    "SELECT id, trim('  ' || customer || ' ') AS t, ltrim(customer, 'a') AS l,"
    " rtrim(customer, 'y') AS r FROM orders",
    "SELECT id, strpos(customer, 'a') AS p, position('d' IN customer) AS q,"
    " contains(customer, 'd') AS c, starts_with(customer, 'a') AS s, ends_with(customer, 'b') AS e,"
    " prefix(customer, 'c') AS pf, suffix(customer, 'y') AS sf FROM orders",
    "SELECT id FROM orders WHERE customer LIKE 'a%' OR customer NOT LIKE '_o_'",
    "SELECT id, customer ILIKE 'ADA' AS i, customer NOT ILIKE '%B' AS n FROM orders",
    "SELECT id, customer || '!' AS a, concat(customer, '-', customer) AS b,"
    " replace(customer, 'a', 'A') AS r, repeat(customer, qty) AS t, left(customer, 2) AS f,"
    " upper(customer) AS u, lower(customer) AS lo FROM orders",
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


@pytest.mark.parametrize(
    ("query", "message"),
    [
        ("SELECT reverse(customer) FROM orders", "grapheme clusters"),
        ("SELECT id FROM orders WHERE customer LIKE 'a\\%'", "backslash"),
        ("SELECT id FROM orders WHERE customer LIKE customer", "not a constant"),
        ("SELECT substring(customer, 1, -1) FROM orders", "negative length"),
        # DuckDB raises outside these (#336).
        ("SELECT substring(customer, 4294967296, 2) FROM orders", "offset 4294967296 is outside"),
        ("SELECT substring(customer, -4294967297, 2) FROM orders", "offset -4294967297"),
        ("SELECT substring(customer, 0, 4294967296) FROM orders", "length 4294967296 is outside"),
        (
            "SELECT substring(customer, 9223372036854775807, 9223372036854775807) FROM orders",
            "outside DuckDB's supported range",
        ),
        ("SELECT customer || 1 FROM orders", "|| of a int32"),
    ],
)
def test_refusals_say_what(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, SCHEMAS)

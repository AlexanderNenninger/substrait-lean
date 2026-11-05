"""Strings in DuckDB SQL through sverify's own lift (`sverify.sql_lift`):
oracles A and C, and the refusals."""

import json

import ibis
import pytest

from _sql_lift import SCHEMAS, TABLES
from sverify.engine import run_checker
from sverify.plan_json import Unsupported as Refused
from sverify.sql_lift import lift
from sverify_dev.lift import check

SCHEMA_T = ibis.schema({"s": "string", "a": "int64"})

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
    # Digests: lowercase hex of the UTF-8 bytes (#725), and the surrogate key
    # dbt_utils.generate_surrogate_key writes.
    "SELECT id, md5(customer) AS m, sha256(customer) AS s FROM orders",
    "SELECT md5(cast(coalesce(cast(id AS TEXT), '_dbt_utils_surrogate_key_null_') || '-'"
    " || coalesce(cast(customer AS TEXT), '_dbt_utils_surrogate_key_null_') AS TEXT)) AS k"
    " FROM orders",
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
        ("SELECT customer || 1 FROM orders", "|| of a int32"),
        ("SELECT sha2(customer, 512) FROM orders", "length other than 256"),
    ],
)
def test_refusals_say_what(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, SCHEMAS)


def _kinds(sql: str, **kw) -> list[str]:
    import sverify as sv

    kw.setdefault("infer", False)
    return [i.kind for i in sv.verify(sql, tables=SCHEMAS, counterexamples=0, **kw).errors]


@pytest.mark.parametrize(
    "sql",
    [
        # DuckDB raises outside `[-2³², 2³²)` offsets and `2³²` lengths (#336).
        "SELECT substring(customer, 4294967296, 2) AS s FROM orders",
        "SELECT substring(customer, -4294967297, 2) AS s FROM orders",
        "SELECT substring(customer, 0, 4294967296) AS s FROM orders",
        "SELECT substring(customer, 9223372036854775807, 9223372036854775807) AS s FROM orders",
        # An offset from a column may be anything.
        "SELECT substring(customer, amount) AS s FROM orders",
    ],
)
def test_substring_out_of_range_is_an_error(sql):
    assert "domain error" in _kinds(sql)


def test_substring_in_range_is_proved_safe():
    assert _kinds("SELECT substring(customer, 4294967295, 4294967295) AS s FROM orders") == []
    # The analysis reads no bound from a column's type: even an INTEGER
    # offset needs one in `requires`.
    assert "domain error" in _kinds("SELECT substring(customer, qty, 2) AS s FROM orders")
    sql = "SELECT substring(customer, amount, 2) AS s FROM orders"
    within = {"orders": ["amount >= -4294967296", "amount < 4294967296"]}
    assert "domain error" not in _kinds(sql, requires=within)


@pytest.mark.parametrize("start", [-(2**32) - 1, -(2**40), 2**32, 2**40])
def test_the_written_plan_raises_out_of_range(start):
    # DuckDB raises for the offset it sees; the wrap-around arithmetic shifts
    # a negative one, so the written plan guards it.
    import pyarrow as pa

    from sverify.engine import connect, run_plan, written_plan

    con = connect()
    con.put("t", pa.table({"s": ["hello"], "a": pa.array([start], pa.int64())}))
    plan = json.dumps(lift("SELECT substring(s, a, 2) AS x FROM t", {"t": SCHEMA_T}).plan)
    with pytest.raises(Exception, match="(?i)substring offset outside of supported range"):
        run_plan(con, written_plan(plan), "duckdb")


def test_a_surrogate_key_is_never_null():
    """`md5` of a string that is never NULL is never NULL: the `not_null`
    test of a dbt surrogate key is proved (#725)."""
    import sverify as sv

    key = "md5(cast(coalesce(cast(id AS TEXT), '_n_') || '-' || coalesce(customer, '_n_') AS TEXT))"
    report = sv.verify(
        f"SELECT {key} AS k FROM orders",
        tables=SCHEMAS,
        semantics="duckdb",
        ensures=["k IS NOT NULL"],
        counterexamples=0,
    )
    assert report.proved

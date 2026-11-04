"""CTEs, joins, subqueries, set operations, `TABLE t`, ordering and limits
in DuckDB SQL through sverify's own lift (`sverify.sql_lift`): oracles A
and C, and the refusals."""

import json

import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

import sverify as sv
from _sql_lift import SCHEMAS, TABLES
from sverify.engine import run_checker
from sverify.plan_json import Unsupported as Refused
from sverify.sql_lift import lift
from sverify_dev.lift import check

pytestmark = pytest.mark.backend("duckdb")

#: Queries of the subset, each through oracles A and C.
QUERIES = [
    "SELECT o.id, c.region FROM orders o JOIN customers c ON c.name = o.customer",
    "SELECT o.id, c.region FROM orders o LEFT JOIN customers c ON c.name = o.customer"
    " ORDER BY o.id",
    "SELECT o.id, c.region FROM orders o, customers c WHERE c.name = o.customer AND o.amount > 1",
    "SELECT c.region, sum(o.amount) AS total FROM orders o JOIN customers c"
    " ON c.name = o.customer GROUP BY c.region ORDER BY c.region",
    "SELECT DISTINCT region FROM customers ORDER BY region",
    "SELECT id, price FROM orders ORDER BY price DESC LIMIT 3",
    "SELECT id, price FROM orders ORDER BY price NULLS FIRST, id LIMIT 2 OFFSET 1",
    "SELECT r.region, r.n FROM (SELECT region, count(*) AS n FROM customers GROUP BY region) r"
    " WHERE r.n > 1",
    # CTEs, inlined; uncorrelated subqueries, with SQL's NULLs for IN; semi,
    # anti, right and full joins.
    "WITH big AS (SELECT id, amount * 2 AS a2 FROM orders WHERE amount > 2), eu(n) AS"
    " (SELECT name FROM customers WHERE region = 'eu') SELECT big.id, big.a2 FROM big"
    " JOIN orders o ON o.id = big.id JOIN eu ON eu.n = o.customer",
    "SELECT id FROM orders WHERE customer IN (SELECT name FROM customers WHERE region = 'eu')",
    "SELECT id, customer NOT IN (SELECT name FROM customers) AS stranger FROM orders",
    "SELECT id FROM orders WHERE amount > (SELECT avg(amount) FROM orders)",
    "SELECT id, (SELECT count(*) FROM customers) AS n FROM orders"
    " WHERE EXISTS (SELECT 1 FROM customers WHERE region = 'us')",
    "SELECT * FROM orders SEMI JOIN customers ON customers.name = orders.customer",
    "SELECT * FROM orders ANTI JOIN customers ON customers.name = orders.customer",
    "SELECT o.id, c.name FROM orders o RIGHT JOIN customers c ON c.name = o.customer",
    "SELECT o.id, c.name FROM orders o FULL JOIN customers c ON c.name = o.customer",
    # ORDER BY expressions over output columns.
    "SELECT customer, sum(amount) AS s FROM orders GROUP BY customer"
    " ORDER BY CASE WHEN s > 6 THEN customer END, customer",
    # Set operations (#344): NULLs equal, multiplicities for ALL, the common
    # column type, and ORDER BY/LIMIT over the whole operation.
    "SELECT customer FROM orders UNION ALL SELECT name FROM customers",
    "SELECT customer FROM orders UNION SELECT name FROM customers ORDER BY customer NULLS FIRST",
    "SELECT customer FROM orders EXCEPT SELECT name FROM customers",
    "SELECT customer FROM orders EXCEPT ALL SELECT name FROM customers",
    "SELECT customer FROM orders INTERSECT SELECT name FROM customers",
    "SELECT customer FROM orders INTERSECT ALL SELECT name FROM customers",
    "SELECT qty FROM orders UNION SELECT amount FROM orders ORDER BY qty IS NULL, qty LIMIT 4",
    "SELECT c FROM (SELECT customer AS c FROM orders INTERSECT SELECT name FROM customers)",
    "WITH c AS (SELECT name FROM customers UNION ALL SELECT name FROM customers)"
    " SELECT name, count(*) AS n FROM c GROUP BY name",
    "TABLE customers EXCEPT ALL SELECT name, region FROM customers WHERE region = 'eu'",
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


def test_sorts_put_nulls_last_unless_told():
    plan = lift("SELECT id FROM orders ORDER BY price DESC, qty NULLS FIRST", SCHEMAS).plan
    sort = plan["relations"][0]["root"]["input"]
    while "sort" not in sort:
        sort = next(v for v in sort.values() if isinstance(v, dict) and "input" in v)["input"]
    directions = [k["direction"] for k in sort["sort"]["sorts"]]
    assert directions == ["SORT_DIRECTION_DESC_NULLS_LAST", "SORT_DIRECTION_ASC_NULLS_FIRST"]


@pytest.mark.parametrize(
    ("query", "message"),
    [
        ("SELECT id FROM orders UNION BY NAME SELECT id FROM orders", "UNION BY NAME"),
        (
            "WITH RECURSIVE t(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM t) SELECT n FROM t",
            "RECURSIVE",
        ),
        (
            "SELECT id FROM orders o"
            " WHERE EXISTS (SELECT 1 FROM customers WHERE name = o.customer)",
            "correlated",
        ),
        # Joins that are not the inner join of their ON, and a star SQLGlot
        # expands otherwise than DuckDB.
        ("SELECT id FROM orders ASOF JOIN customers ON customer >= name", "ASOF JOIN"),
        ("SELECT id FROM orders POSITIONAL JOIN customers", "POSITIONAL JOIN"),
        # What SQLGlot hangs on a table.
        ("FROM orders o1, orders o2 SELECT count(*)", "with joins"),
        ("SELECT count(*) FROM orders TABLESAMPLE 2 ROWS", "with sample"),
        ("SELECT * FROM orders PIVOT (sum(amount) FOR customer IN ('ada'))", "with pivots"),
        (
            "SELECT orders.*, c.* FROM orders FULL JOIN customers AS c (customer, region)"
            " USING (customer)",
            "with JOIN … USING",
        ),
        ("SELECT id FROM elsewhere", "cannot resolve"),
        ("SELECT * FROM orders o JOIN orders p ON o.id = p.id", "two output columns named id"),
        ("SELECT id FROM orders LIMIT qty", "LIMIT"),
    ],
)
def test_refusals_say_what(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, SCHEMAS)


# #344: INTERSECT and EXCEPT [ALL] keep multiplicities as DuckDB does, with
# NULLs equal; `TABLE t` is `SELECT * FROM t`.
SETS = ibis.schema({"x": "int64", "s": "string"})
set_rows = st.lists(
    st.tuples(st.none() | st.integers(0, 2), st.none() | st.sampled_from(["a", "b"])), max_size=7
)


@settings(max_examples=40, deadline=None, suppress_health_check=list(HealthCheck))
@given(a=set_rows, b=set_rows)
def test_set_operations_keep_duckdbs_multiplicities(a, b):
    from sverify.engine import connect, create_table, run_plan, written_plan
    from sverify.testing import duckdb_sql, inline_tables, lean_values

    con = connect()
    create_table(con, "a", SETS, a)
    create_table(con, "b", SETS, b)
    for op in ("UNION", "UNION ALL", "EXCEPT", "EXCEPT ALL", "INTERSECT", "INTERSECT ALL"):
        sql = f"TABLE a {op} TABLE b"
        plan = json.dumps(lift(sql, {"a": SETS, "b": SETS}, "duckdb").plan)
        want = sorted(repr(tuple(r.values())) for r in duckdb_sql(con, sql).to_pylist())
        inlined = inline_tables(json.loads(plan), {"a": a, "b": b})
        assert sorted(map(repr, lean_values(json.dumps(inlined)))) == want, op
        got = run_plan(con, written_plan(plan), "duckdb").to_pylist()
        assert sorted(repr(tuple(r.values())) for r in got) == want, op


@pytest.mark.parametrize(
    ("sql", "expanded"),
    [
        ("SELECT 1 EXCEPT ALL TABLE t", "SELECT 1 EXCEPT ALL (SELECT * FROM t)"),
        ("(TABLE a EXCEPT ALL TABLE b)", "((SELECT * FROM a) EXCEPT ALL (SELECT * FROM b))"),
        ('TABLE "my t"', '(SELECT * FROM "my t")'),
        ("SELECT table_name FROM t", "SELECT table_name FROM t"),
    ],
)
def test_table_shorthand(sql, expanded):
    """SQLGlot does not parse DuckDB's `TABLE t` (upstream/bugs/SG-6.json)."""
    from sverify.sql_lift import expand_table_shorthand

    assert expand_table_shorthand(sql) == expanded


def test_all_set_operations_are_determined_by_keys():
    """INTERSECT ALL and EXCEPT ALL number equal rows with a window: reported
    as determined when the inputs have keys (the rows are then distinct)."""
    sql = "SELECT x, s FROM a EXCEPT ALL SELECT x, s FROM b"
    tables = {"a": SETS, "b": SETS}
    assert sv.verify("SELECT x, s FROM a EXCEPT SELECT x, s FROM b", tables=tables).deterministic
    keyed = {"a": [sv.unique("x")], "b": [sv.unique("x")]}
    assert sv.verify(sql, tables=tables, requires=keyed).deterministic

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
    # #1939: a WITH in front of a set operation covers its branches.
    "WITH c AS (SELECT name FROM customers) SELECT name FROM c UNION ALL"
    " SELECT customer FROM orders",
    "WITH c AS (SELECT name FROM customers) SELECT name FROM c EXCEPT SELECT customer FROM orders"
    " ORDER BY name",
    # #1991: GROUP BY ALL groups by the items without an aggregate; QUALIFY filters a window.
    "SELECT customer, sum(amount) AS s FROM orders GROUP BY ALL",
    "SELECT customer, qty, count(*) AS n, max(price) AS m FROM orders GROUP BY ALL ORDER BY 1, 2",
    "SELECT sum(amount) AS s, count(*) AS n FROM orders GROUP BY ALL",
    "SELECT customer, qty + 1 AS q FROM orders GROUP BY ALL HAVING count(*) > 0",
    "SELECT id, customer, amount FROM orders QUALIFY row_number() OVER"
    " (PARTITION BY customer ORDER BY amount DESC, id) = 1",
    "SELECT customer, amount, rank() OVER (PARTITION BY customer ORDER BY amount) AS r FROM orders"
    " QUALIFY r <= 2",
    # A star keeps the table's columns, without the rewrite's window column.
    "SELECT * FROM orders QUALIFY row_number() OVER"
    " (PARTITION BY customer ORDER BY amount, id) = 1",
    "SELECT * FROM orders QUALIFY rank() OVER (ORDER BY amount, id) <= 2"
    " AND row_number() OVER (ORDER BY id) = 1",
    "SELECT o.* FROM orders o QUALIFY rank() OVER (PARTITION BY customer ORDER BY amount, id) = 1",
    "TABLE customers EXCEPT ALL SELECT name, region FROM customers WHERE region = 'eu'",
    # #803: VALUES in FROM and as a CTE, typed across rows.
    "SELECT * FROM (VALUES (1, 'a'), (2, 'b'), (NULL, 'c')) v(k, s)",
    "SELECT o.id, m.label FROM orders o JOIN (VALUES ('ada', 1.5), ('bob', 2)) m(name, label)"
    " ON m.name = o.customer",
    "WITH m(name, grp) AS (VALUES ('ada', 'a'), ('cy', NULL)) SELECT c.name, m.grp"
    " FROM customers c LEFT JOIN m ON m.name = c.name",
    "SELECT col0 + col1 AS s FROM (VALUES (1, 2), (3, 4))",
    # #804: UNPIVOT, and its UNNEST form, as a UNION ALL.
    "SELECT id, k, v FROM orders UNPIVOT (v FOR k IN (amount, qty))",
    "SELECT * FROM (SELECT id, qty, price FROM orders) UNPIVOT INCLUDE NULLS"
    " (v FOR k IN (qty, price AS 'p'))",
    "SELECT u.k, count(*) AS n FROM orders UNPIVOT (v FOR k IN (amount, qty)) AS u GROUP BY u.k",
    "SELECT id, unnest(['amount', 'qty']) AS k, unnest([amount, qty]) AS v FROM orders",
    "SELECT id, unnest([price, amount, NULL]) AS v FROM orders WHERE id > 2",
    # #805: ASOF [LEFT] JOIN, each direction.
    "SELECT a.id, b.id AS prev FROM orders a ASOF JOIN orders b"
    " ON a.customer = b.customer AND a.placed > b.placed",
    "SELECT a.id, b.id AS prev FROM orders a ASOF LEFT JOIN orders b"
    " ON a.customer = b.customer AND a.placed >= b.placed",
    "SELECT a.id, b.id AS next FROM orders a ASOF LEFT JOIN orders b ON b.placed > a.placed",
    "SELECT o.id, p.amount AS above FROM orders o ASOF LEFT JOIN orders p ON o.amount < p.amount",
    "SELECT a.id, b.id AS nxt FROM orders a ASOF JOIN orders b ON a.day < b.day"
    " AND a.customer IS NOT DISTINCT FROM b.customer",
    # #345: a correlated [NOT] EXISTS that is a conjunct of WHERE, as a semi or
    # anti join. NULL keys (orders 5, no customer) match nothing.
    "SELECT id FROM orders o WHERE EXISTS (SELECT 1 FROM customers c WHERE c.name = o.customer)",
    "SELECT id FROM orders o WHERE NOT EXISTS (SELECT 1 FROM customers c"
    " WHERE c.name = o.customer)",
    "SELECT name FROM customers c WHERE EXISTS (SELECT * FROM orders o WHERE o.customer = c.name"
    " AND o.amount > 5)",
    # A condition that is not an equality, and an inner-only conjunct.
    "SELECT id FROM orders o WHERE EXISTS (SELECT 1 FROM orders p WHERE p.amount > o.amount"
    " AND p.id <> o.id)",
    "SELECT id FROM orders o WHERE EXISTS (SELECT 1 FROM customers c WHERE c.name = o.customer"
    " AND c.region = 'eu') AND o.amount > 1",
    # Two of them, an empty inner table, and the other conjuncts first.
    "SELECT id FROM orders o WHERE o.amount > 0 AND EXISTS (SELECT 1 FROM customers c"
    " WHERE c.name = o.customer) AND NOT EXISTS (SELECT 1 FROM customers c"
    " WHERE c.name = o.customer AND c.region = 'us')",
    "SELECT id FROM orders o WHERE EXISTS (SELECT 1 FROM customers c WHERE c.name = o.customer"
    " AND c.region = 'nowhere')",
    "SELECT id FROM orders o WHERE NOT EXISTS (SELECT 1 FROM customers c WHERE c.name = o.customer"
    " AND c.region = 'nowhere')",
    # Names resolve innermost first: the inner `customer` is the inner row's own
    # (a tautology where it is not NULL), and the same table on both sides.
    "SELECT id FROM orders WHERE EXISTS (SELECT 1 FROM orders o2 WHERE o2.customer = customer)",
    "SELECT id FROM orders WHERE EXISTS (SELECT 1 FROM orders WHERE orders.id = id)",
    # A join inside the subquery, and a condition that can raise (division by
    # an inner column) in a semi join.
    "SELECT name FROM customers c WHERE EXISTS (SELECT 1 FROM orders o JOIN customers d"
    " ON d.name = o.customer WHERE d.region = c.region AND o.id > 1)",
    "SELECT id FROM orders o WHERE EXISTS (SELECT 1 FROM orders p WHERE p.id = o.id"
    " AND 10 / p.amount > 0)",
    # #345: a correlated IN and NOT IN, a conjunct of WHERE. `qty` has NULLs
    # (order 2) and the NULL customer (order 5) correlates with nothing.
    "SELECT id FROM orders o WHERE o.qty IN (SELECT p.qty FROM orders p"
    " WHERE p.customer = o.customer)",
    "SELECT id FROM orders o WHERE o.qty NOT IN (SELECT p.qty FROM orders p"
    " WHERE p.customer = o.customer)",
    "SELECT id FROM orders o WHERE o.qty NOT IN (SELECT p.qty FROM orders p"
    " WHERE p.customer = o.customer AND p.id <> o.id)",
    # NULL in the subquery's column against a non-NULL needle, and an empty one.
    "SELECT id FROM orders o WHERE CAST(o.amount AS INTEGER) NOT IN (SELECT p.qty FROM orders p"
    " WHERE p.customer = o.customer)",
    "SELECT id FROM orders o WHERE o.qty NOT IN (SELECT p.qty FROM orders p"
    " WHERE p.customer = o.customer AND p.id < 0)",
    "SELECT id FROM orders o WHERE o.qty IN (SELECT p.qty FROM orders p"
    " WHERE p.customer = o.customer AND p.id < 0)",
    # A needle that is an expression, a condition that is NULL (`price`), a plain
    # conjunct beside it, and inner-only conjuncts.
    "SELECT id FROM orders o WHERE o.amount + 1 IN (SELECT p.amount FROM orders p"
    " WHERE p.price > o.price) AND o.id > 0",
    "SELECT id FROM orders o WHERE o.id NOT IN (SELECT p.id FROM orders p"
    " WHERE p.price < o.price AND p.amount > 1)",
    "SELECT name FROM customers c WHERE c.name IN (SELECT o.customer FROM orders o"
    " WHERE o.customer = c.name AND o.amount > 5)",
    "SELECT name FROM customers c WHERE c.name NOT IN (SELECT o.customer FROM orders o"
    " WHERE o.amount > 5 AND c.region <> 'us')",
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
        # Correlated EXISTS shapes that stay refused, each by name (#345).
        (
            "SELECT id FROM orders o WHERE amount > 0 OR EXISTS"
            " (SELECT 1 FROM customers WHERE name = o.customer)",
            "correlated",
        ),
        (
            "SELECT id, EXISTS (SELECT 1 FROM customers WHERE name = o.customer) AS known"
            " FROM orders o",
            "correlated",
        ),
        (
            "SELECT id FROM orders o WHERE NOT (amount > 3 AND EXISTS"
            " (SELECT 1 FROM customers WHERE name = o.customer))",
            "correlated",
        ),
        (
            "SELECT id FROM orders o WHERE EXISTS (SELECT 1 FROM customers"
            " GROUP BY name HAVING min(name) = o.customer)",
            "correlated|GROUP BY",
        ),
        (
            "SELECT id FROM orders o WHERE EXISTS (SELECT 1 FROM customers WHERE name = o.customer"
            " UNION SELECT 1 FROM customers)",
            "set operation",
        ),
        (
            "SELECT id FROM orders o WHERE amount > 0 OR o.qty IN (SELECT p.qty FROM orders p"
            " WHERE p.customer = o.customer)",
            "correlated",
        ),
        (
            "SELECT id, o.qty IN (SELECT p.qty FROM orders p WHERE p.customer = o.customer) AS m"
            " FROM orders o",
            "correlated",
        ),
        (
            "SELECT id FROM orders o WHERE o.qty IN (SELECT o.amount FROM orders p"
            " WHERE p.customer = o.customer)",
            "reads the outer",
        ),
        (
            "SELECT id FROM orders o WHERE o.qty IN (SELECT p.qty, p.id FROM orders p"
            " WHERE p.customer = o.customer)",
            "one column",
        ),
        (
            "SELECT id FROM orders o WHERE o.qty IN (SELECT p.qty FROM orders p"
            " WHERE p.customer = o.customer UNION SELECT 1 FROM orders)",
            "set operation",
        ),
        (
            "SELECT id FROM orders o WHERE o.qty NOT IN (SELECT p.qty FROM orders p"
            " WHERE p.customer = o.customer LIMIT 1)",
            "LIMIT in a correlated IN",
        ),
        (
            "SELECT id FROM orders o WHERE EXISTS (SELECT 1 FROM customers WHERE name = o.customer"
            " LIMIT 1)",
            "LIMIT in a correlated EXISTS",
        ),
        (
            "SELECT id FROM orders o WHERE EXISTS (SELECT amount + 1 FROM customers"
            " WHERE name = o.customer)",
            "write SELECT 1",
        ),
        (
            "SELECT id FROM orders o WHERE EXISTS (SELECT 1 FROM customers c JOIN orders p"
            " ON p.customer = o.customer WHERE c.name = p.customer)",
            "correlated",
        ),
        (
            "SELECT id FROM orders o WHERE EXISTS (SELECT 1 FROM customers c WHERE c.name ="
            " o.customer AND c.region IN (SELECT region FROM customers WHERE name = o.customer))",
            "subquery, window or aggregate",
        ),
        # Joins that are not the inner join of their ON, and a star SQLGlot
        # expands otherwise than DuckDB.
        ("SELECT id FROM orders ASOF RIGHT JOIN customers ON customer >= name", "ASOF RIGHT"),
        ("SELECT id FROM orders ASOF JOIN customers ON customer = name", "exactly one of"),
        (
            "SELECT * FROM orders UNPIVOT ((a, b) FOR k IN ((amount, qty), (price, cost)))",
            "several value columns|only columns",
        ),
        ("SELECT * FROM (VALUES (1), (amount)) v(x)", "cannot resolve|computed"),
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
        (
            "SELECT customer, sum(amount) OVER () AS s FROM orders GROUP BY ALL",
            "GROUP BY ALL with a window function",
        ),
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
    from sverify.engine import connect, run_plan, written_plan
    from sverify.testing import duckdb_sql, inline_tables, lean_values

    con = connect()
    con.create("a", SETS, a)
    con.create("b", SETS, b)
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

"""DuckDB SQL through sverify's own lift (`sverify.sql_lift`, #239):
`sv.sql(query, dialect="duckdb", semantics=...)`, its two profiles, its
refusals, and oracles A and C (`sverify_dev.lift`)."""

import datetime as dt
import json
from decimal import Decimal
from typing import Any

import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

import sverify as sv
from _pipelines import arrow_table as table
from _pipelines import rows
from sverify.engine import run_checker
from sverify.engines import Unsupported
from sverify.errors import VerificationError
from sverify.io import StaticSource
from sverify.plan_json import Unsupported as Refused
from sverify.sql_lift import DUCKDB, REFERENCE, lift
from sverify_dev import catalogue
from sverify_dev.lift import check, score

pytestmark = pytest.mark.backend("duckdb")

ORDERS = pa.schema(
    [
        pa.field("id", pa.int64(), nullable=False),
        pa.field("customer", pa.string()),
        pa.field("amount", pa.int64(), nullable=False),
        pa.field("qty", pa.int32()),
        pa.field("price", pa.float64()),
        pa.field("cost", pa.decimal128(15, 2)),
        pa.field("day", pa.date32()),
        pa.field("placed", pa.timestamp("us")),
    ]
)
CUSTOMERS = pa.schema([pa.field("name", pa.string()), pa.field("region", pa.string())])

ORDER_ROWS = [
    (1, "ada", 5, 3, 2.5, Decimal("10.50"), dt.date(2024, 1, 1), dt.datetime(2024, 1, 1, 9, 30)),
    (2, "bob", 7, None, 0.0, Decimal("3.25"), dt.date(2024, 1, 2), dt.datetime(2024, 1, 7, 23, 59)),
    (3, "ada", 0, 4, -1.5, None, dt.date(2024, 2, 1), None),
    (4, "cy", 9, 2, None, Decimal("0.01"), None, dt.datetime(2023, 12, 31, 0, 0, 1)),
    (5, None, 2, 7, 10.0, Decimal("99.99"), dt.date(2023, 12, 31), dt.datetime(2024, 3, 31, 12)),
]
CUSTOMER_ROWS = [("ada", "eu"), ("bob", "us"), ("dan", "eu")]
TABLES = {"orders": table(ORDERS, ORDER_ROWS), "customers": table(CUSTOMERS, CUSTOMER_ROWS)}
SCHEMAS = {n: ibis.Schema.from_pyarrow(t.schema) for n, t in TABLES.items()}

#: Queries of the subset, each through oracles A and C.
QUERIES = [
    # A double's negation in a plan with decimals is written back as it reads
    # (TPC-DS q89's `-(sum_sales - avg_monthly_sales)`).
    "SELECT customer, s, -(s - avg(s) OVER ()) AS x"
    " FROM (SELECT customer, sum(cost) AS s FROM orders GROUP BY customer)",
    # DuckDB's AVG of a DECIMAL is a DOUBLE: the exact sum by the count, over
    # a window too, and arithmetic with it is in doubles (TPC-DS q89).
    "SELECT customer, avg(cost) OVER (PARTITION BY customer) AS a FROM orders",
    "SELECT id, cost - avg(cost) OVER (PARTITION BY customer) AS dev FROM orders",
    # DuckDB's AVG of a DECIMAL is a DOUBLE: the exact sum by the count.
    "SELECT customer, avg(cost) AS a FROM orders GROUP BY customer",
    "SELECT avg(cost) AS a FROM orders WHERE id > 100",
    "SELECT id, amount * 2 AS a2, qty + 1 AS q1, -amount AS neg FROM orders WHERE amount > 1",
    "SELECT id, amount / 2 AS half, amount // 2 AS q, amount % 3 AS m FROM orders",
    "SELECT id, amount / qty AS r, price / 2 AS p FROM orders",
    "SELECT id FROM orders WHERE price > 1.5 AND qty BETWEEN 2 AND 4 OR customer IS NULL",
    "SELECT id FROM orders WHERE NOT (customer IN ('ada', 'cy')) AND customer IS NOT NULL",
    "SELECT id, CASE WHEN qty > 3 THEN 'big' WHEN qty IS NULL THEN NULL ELSE 'small' END AS k,"
    " CASE qty WHEN 3 THEN 1.5 ELSE 2 END AS c, coalesce(qty, 0) AS z FROM orders",
    "SELECT id, CAST(qty AS DOUBLE) / 4 AS x, CAST(amount AS INTEGER) AS i,"
    " CAST(qty AS BIGINT) AS b FROM orders",
    "SELECT id, cost * cost AS c2, cost + 1 AS c1, cost * 2 AS cd, cost > 3.5 AS big FROM orders",
    "SELECT id FROM orders WHERE day >= DATE '2024-01-01' AND day < '2024-02-01'",
    "SELECT customer, count(*) AS n, sum(amount) AS total, avg(qty) AS a, min(amount) AS lo,"
    " max(day) AS last, sum(cost) AS c, count(DISTINCT qty) AS dq"
    " FROM orders GROUP BY customer HAVING count(*) >= 1 ORDER BY total DESC",
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
    "SELECT qty, count(*) FROM orders GROUP BY 1 ORDER BY 2 DESC, 1",
    "SELECT count(*) AS n, sum(qty) AS s FROM orders WHERE amount > 100",
    "SELECT 1 + 1 AS two, 7 // 2 AS q, 1 // 1 AS one",
    "SELECT id, date_trunc('day', placed) AS d, date_trunc('week', placed) AS w,"
    " date_trunc('quarter', placed) AS q, date_trunc('hour', placed) AS h FROM orders",
    "SELECT id, placed + INTERVAL 1 DAY AS tomorrow, placed - INTERVAL '90' MINUTES AS before,"
    " INTERVAL 2 MONTHS + placed AS later FROM orders"
    " WHERE placed >= TIMESTAMP '2024-01-08' - INTERVAL 1 WEEK",
    "SELECT date_trunc('month', placed) AS m, count(*) AS n FROM orders GROUP BY 1 ORDER BY 1",
    # DuckDB's DATE ± INTERVAL and date_trunc of a DATE are TIMESTAMPs at
    # midnight: held as dates, compared exactly.
    "SELECT id FROM orders WHERE day <= DATE '2024-03-31' - INTERVAL 90 DAY",
    "SELECT id FROM orders WHERE day >= DATE '2023-12-31' AND day < DATE '2023-12-31'"
    " + INTERVAL 1 MONTH",
    "SELECT id FROM orders WHERE day + INTERVAL 1 MONTH > DATE '2024-02-15'",
    "SELECT DATE '2024-01-31' + INTERVAL 1 MONTH AS m, DATE '2024-01-01' + INTERVAL 1 HOUR AS h",
    "SELECT id FROM orders WHERE date_trunc('month', day) = DATE '2024-01-01'",
    "SELECT id, extract(year FROM day) AS y, extract(quarter FROM day) AS q, month(day) AS m,"
    " day(day) AS d, dayofweek(day) AS dw, dayofyear(day) AS dy, week(day) AS w FROM orders",
    "SELECT id, date_part('hour', placed) AS h, minute(placed) AS mi, second(placed) AS s,"
    " extract(dow FROM placed) AS dw FROM orders",
    "SELECT id, day - DATE '2024-01-01' AS since, datediff('day', DATE '2024-01-01', day) AS dd"
    " FROM orders",
    "SELECT extract(year FROM day) AS y, count(*) AS n FROM orders GROUP BY 1 ORDER BY 1",
    # Strings: DuckDB counts characters (code points) from 1; LIKE has no
    # escape character; `||` is NULL with a NULL, `concat` leaves NULLs out.
    "SELECT id, length(customer) AS l, substring(customer, 2, 2) AS a,"
    " substring(customer, -2, 2) AS b, substring(customer, 0, 2) AS c, substr(customer, 2) AS d"
    " FROM orders",
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
    # Window functions; ties only where the function is the same on them.
    "SELECT id, row_number() OVER (PARTITION BY customer ORDER BY id) AS rn,"
    " rank() OVER (ORDER BY customer) AS r, dense_rank() OVER (ORDER BY customer) AS d"
    " FROM orders",
    "SELECT id, lag(amount) OVER (ORDER BY id) AS p, lead(amount, 2, -1) OVER (ORDER BY id DESC)"
    " AS n, first_value(amount) OVER (PARTITION BY customer ORDER BY id) AS f FROM orders",
    "SELECT id, sum(amount) OVER (PARTITION BY customer) AS s, avg(price) OVER () AS a,"
    " sum(amount) OVER (ORDER BY id) AS run,"
    " max(amount) OVER (ORDER BY id ROWS BETWEEN 1 PRECEDING AND 1 FOLLOWING) AS m FROM orders",
    "SELECT id, ntile(2) OVER (ORDER BY id) AS nt, percent_rank() OVER (ORDER BY id) AS pr,"
    " cume_dist() OVER (ORDER BY id) AS cd, lag(amount * 2) OVER (ORDER BY id) AS l2 FROM orders",
    "SELECT customer, sum(amount) AS s, rank() OVER (ORDER BY sum(amount) DESC) AS r,"
    " avg(sum(amount)) OVER () AS a FROM orders GROUP BY customer",
    # Numbers: DuckDB's `power` and elementary functions are of doubles; its
    # `greatest`/`least` leave NULLs out; `log(x)` is base 10.
    "SELECT id, power(amount, 2) AS p, amount ** 2 AS q, abs(qty) AS a, abs(price) AS af,"
    " sign(price) AS s, isnan(price) AS n FROM orders",
    "SELECT id, round(price) AS r, round(price, 1) AS r1, floor(price) AS f, ceil(price) AS c,"
    " floor(qty) AS fq, round(qty) AS rq FROM orders",
    "SELECT id, greatest(amount, qty, 4) AS g, least(amount, qty) AS l, nullif(amount, 0) AS z,"
    " qty IS DISTINCT FROM 3 AS d, qty IS NOT DISTINCT FROM NULL AS nn FROM orders",
    "SELECT id, sqrt(amount + 1) AS s, ln(amount + 1) AS l, log(amount + 1) AS lg,"
    " log2(amount + 1) AS l2, log(3, amount + 1) AS lb, exp(qty) AS e, sin(price) AS si"
    " FROM orders",
    # DISTINCT and FILTER in aggregates.
    "SELECT customer, count(DISTINCT qty) AS n, sum(DISTINCT amount) AS s,"
    " sum(amount) FILTER (WHERE amount > 2) AS big, count(*) FILTER (WHERE qty IS NULL) AS nq"
    " FROM orders GROUP BY customer",
    "SELECT id, placed + INTERVAL '1 month 2 days 3 hours' AS later FROM orders"
    " WHERE day >= ' 2024-01-01'",
    "SELECT id, amount / 0 AS inf, price / 0 AS p FROM orders",
    # Grouping sets: one aggregate per set, UNION ALL'd; GROUPING() is a
    # constant of each.
    "SELECT customer, qty, sum(amount) AS s, count(*) AS n FROM orders"
    " GROUP BY ROLLUP (customer, qty)",
    "SELECT customer, qty, GROUPING(customer) AS g, GROUPING(customer, qty) AS gg, avg(price) AS p"
    " FROM orders GROUP BY CUBE (customer, qty)",
    "SELECT customer, day, count(*) AS n FROM orders"
    " GROUP BY GROUPING SETS ((customer, day), (customer), ())",
    "SELECT customer, qty, sum(amount) AS s FROM orders GROUP BY customer, ROLLUP (qty)"
    " HAVING GROUPING(qty) = 1 OR sum(amount) > 4",
    "SELECT customer, GROUPING(customer) AS g,"
    " rank() OVER (PARTITION BY GROUPING(customer) ORDER BY sum(amount)) AS r"
    " FROM orders GROUP BY ROLLUP (customer) ORDER BY g DESC, customer",
    "SELECT customer, sum(amount) AS s FROM orders WHERE id > 99 GROUP BY ROLLUP (customer)",
    # Computed window partitions and ORDER BY expressions over output columns.
    "SELECT id, rank() OVER (PARTITION BY amount % 2 ORDER BY -amount, id) AS r FROM orders",
    "SELECT customer, sum(amount) AS s FROM orders GROUP BY customer"
    " ORDER BY CASE WHEN s > 6 THEN customer END, customer",
    # The written plan's division of two double literals (#96, fixed with #335).
    "SELECT 7 / 2 AS h",
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


def test_the_profiles_differ_only_in_what_functions_do():
    fields = DUCKDB.__dataclass_fields__
    assert {f for f in fields if getattr(DUCKDB, f) != getattr(REFERENCE, f)} == {
        "name",
        "float_to_int",
        "decimal_to_int",
        "domain_error",
        "log_zero",
    }


def options(plan: dict, name: str) -> list[list[dict]]:
    """The options of each call of `name` in `plan`."""
    anchors = {
        e["extensionFunction"]["functionAnchor"]
        for e in plan["extensions"]
        if e["extensionFunction"]["name"] == name
    }
    found = []

    def walk(j):
        if isinstance(j, dict):
            f = j.get("scalarFunction")
            if f is not None and f["functionReference"] in anchors:
                found.append(f.get("options", []))
            for v in j.values():
                walk(v)
        elif isinstance(j, list):
            for v in j:
                walk(v)

    walk(plan)
    return found


def test_division_states_its_meaning():
    query = "SELECT amount / qty AS r, amount // qty AS q FROM orders"
    duck, ref = (lift(query, SCHEMAS, s).plan for s in ("duckdb", "reference"))
    zero = {"name": "on_division_by_zero"}
    # `/` divides doubles: by zero DuckDB gives inf, the reference raises.
    assert options(duck, "divide")[0] == [{**zero, "preference": ["IEEE"]}]
    assert options(ref, "divide")[0] == [{**zero, "preference": ["ERROR"]}]
    # `//` divides integers, and raises by zero in both.
    for plan in (duck, ref):
        assert {**zero, "preference": ["ERROR"]} in options(plan, "divide")[1]
    assert lift(query, SCHEMAS).schema == ibis.schema({"r": "float64", "q": "int64"})


def test_duckdb_types_literals_and_decimals_its_own_way():
    schema = lift(
        "SELECT 1 AS i, 3000000000 AS b, 1.5 AS d, 1e3 AS f, qty + 1 AS q,"
        " cost * cost AS c2, cost + cost AS c1 FROM orders",
        SCHEMAS,
    ).schema
    assert schema == ibis.schema(
        {
            "i": "int32",
            "b": "int64",
            "d": "decimal(2, 1)",
            "f": "float64",
            "q": "int32",
            # DuckDB: a product of two decimals of up to 18 digits has 18.
            "c2": "decimal(18, 4)",
            "c1": "decimal(16, 2)",
        }
    )


def test_sorts_put_nulls_last_unless_told():
    plan = lift("SELECT id FROM orders ORDER BY price DESC, qty NULLS FIRST", SCHEMAS).plan
    sort = plan["relations"][0]["root"]["input"]
    while "sort" not in sort:
        sort = next(v for v in sort.values() if isinstance(v, dict) and "input" in v)["input"]
    directions = [k["direction"] for k in sort["sort"]["sorts"]]
    assert directions == ["SORT_DIRECTION_DESC_NULLS_LAST", "SORT_DIRECTION_ASC_NULLS_FIRST"]


def test_a_double_cast_to_an_integer_depends_on_the_semantics():
    query = "SELECT CAST(price AS INTEGER) AS i FROM orders"
    with pytest.raises(Refused, match="TIE_TO_EVEN"):
        lift(query, SCHEMAS, "duckdb")
    # The reference truncates (#209 R9), which the plan's cast means.
    assert lift(query, SCHEMAS, "reference").schema == ibis.schema({"i": "int32"})


@pytest.mark.parametrize(
    ("query", "message"),
    [
        ("SELECT my_udf(id) FROM orders", "unknown function my_udf"),
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
        ("SELECT sum(id) OVER w FROM orders WINDOW w AS (ORDER BY id)", "WINDOW"),
        ("SELECT count(DISTINCT id) OVER () FROM orders", "DISTINCT in a window"),
        # Joins that are not the inner join of their ON, and a star SQLGlot
        # expands otherwise than DuckDB.
        ("SELECT id FROM orders ASOF JOIN customers ON customer >= name", "ASOF JOIN"),
        ("SELECT id FROM orders POSITIONAL JOIN customers", "POSITIONAL JOIN"),
        # What SQLGlot hangs on a table, and literals it reads otherwise.
        ("FROM orders o1, orders o2 SELECT count(*)", "with joins"),
        ("SELECT count(*) FROM orders TABLESAMPLE 2 ROWS", "with sample"),
        ("SELECT * FROM orders PIVOT (sum(amount) FOR customer IN ('ada'))", "with pivots"),
        ("SELECT 1__2", "underscore not between two digits"),
        ("SELECT 1._5", "underscore not between two digits"),
        ("SELECT '1e38'::DECIMAL(38,0)", "does not fit"),
        ('SELECT 42::TINYINT::"null"', "CAST to"),
        ("SELECT INTERVAL 2 DAYS AS x", "INTERVAL output column"),
        (
            "SELECT orders.*, c.* FROM orders FULL JOIN customers AS c (customer, region)"
            " USING (customer)",
            "with JOIN … USING",
        ),
        ("SELECT GROUPING(id) FROM orders GROUP BY ROLLUP (customer)", "GROUPING of"),
        ("SELECT sum(id) OVER (ORDER BY id GROUPS 1 PRECEDING) FROM orders", "GROUPS frames"),
        ("SELECT nope FROM orders", "cannot resolve"),
        ("SELECT id FROM elsewhere", "cannot resolve"),
        ("SELECT id, customer FROM orders GROUP BY id", "GROUP BY"),
        ("SELECT * FROM orders o JOIN orders p ON o.id = p.id", "two output columns named id"),
        ("SELECT TRY_CAST(id AS INT) FROM orders", "TRY_CAST"),
        ("SELECT id FROM orders LIMIT qty", "LIMIT"),
        ("SELECT 170141183460469231731687303715884105727 AS h", "HUGEINT"),
        ("SELEC id FROM orders", "cannot parse"),
        # DuckDB reads `amount` in HAVING as the column, SQLGlot as the alias.
        (
            "SELECT amount + 1 AS amount FROM orders GROUP BY amount HAVING amount = 5",
            "both an input column and an output alias",
        ),
        ("SELECT CAST(price AS HUGEINT) FROM orders", "HUGEINT"),
        ("SELECT CAST(NULL AS INT[3]) FROM orders", "fixed-size array"),
        # A DATE at midnight that DuckDB types a TIMESTAMP needs a cast Lean
        # lacks where it is one: an output column, next to a timestamp column.
        ("SELECT date_trunc('day', day) AS d FROM orders", "is a TIMESTAMP in DuckDB"),
        ("SELECT day + INTERVAL 1 DAY AS d FROM orders", "is a TIMESTAMP in DuckDB"),
        ("SELECT id FROM orders WHERE day < placed", "DATE column as a TIMESTAMP"),
        ("SELECT day + INTERVAL 1 HOUR AS d FROM orders", "hours or less"),
        ("SELECT extract(epoch FROM placed) FROM orders", "date part EPOCH"),
        ("SELECT placed + INTERVAL 'a while' FROM orders", "integers, each with a unit"),
        ("SELECT reverse(customer) FROM orders", "grapheme clusters"),
        ("SELECT id FROM orders WHERE customer LIKE 'a\\%'", "backslash"),
        ("SELECT id FROM orders WHERE customer LIKE customer", "not a constant"),
        ("SELECT substring(customer, 1, -1) FROM orders", "negative length"),
        ("SELECT customer || 1 FROM orders", "|| of a int32"),
    ],
)
def test_refusals_say_what(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, SCHEMAS)


# --------------------------------------------------------------------------
# sv.sql(..., dialect="duckdb")


def sources():
    orders = StaticSource(table(ORDERS, ORDER_ROWS), version=1, name="orders")
    customers = StaticSource(table(CUSTOMERS, CUSTOMER_ROWS), version=1, name="customers")
    return orders, customers


@sv.transform(
    requires={"orders": ["amount >= 0", "qty > 0"]},
    ensures=["total >= 0", "n >= 1", sv.unique("customer")],
)
def per_customer(orders):
    return sv.sql(
        "SELECT customer, sum(amount) AS total, count(*) AS n, avg(qty) AS avg_qty"
        " FROM orders GROUP BY customer",
        dialect="duckdb",
        orders=orders,
    )


def test_a_duckdb_sql_node_is_proved_and_runs_on_duckdb():
    with_qty = [r for r in ORDER_ROWS if r[3] is not None]
    orders = StaticSource(table(ORDERS, with_qty), version=1, name="orders")
    node = per_customer(orders)
    node.refresh(engine="duckdb")
    assert per_customer.last_report is not None and per_customer.last_report.proved
    got = sorted(rows(node), key=repr)
    assert got == sorted([("ada", 5, 2, 3.5), ("cy", 9, 1, 2.0), (None, 2, 1, 7.0)], key=repr)


def test_a_duckdb_sql_step_chains():
    orders, customers = sources()
    step = sv.sql(
        "SELECT o.id, c.region FROM orders o JOIN customers c ON c.name = o.customer",
        dialect="duckdb",
        semantics="reference",
    )
    assert step.dialect == "duckdb" and step.semantics == "reference"
    node = orders.pipe(step, customers=customers)
    node.refresh(engine="duckdb")
    assert sorted(rows(node)) == [(1, "eu"), (2, "us"), (3, "eu")]


def test_an_unproved_ensures_names_the_condition():
    @sv.transform(ensures=["half > 0"])
    def halves(orders):
        return sv.sql("SELECT amount / 2 AS half FROM orders", dialect="duckdb", orders=orders)

    orders, _ = sources()
    with pytest.raises(VerificationError, match="half > 0"):
        halves(orders)


def test_the_semantics_changes_what_the_contract_can_prove():
    # DuckDB's `/` by zero is inf, so a zero divisor is never an error there;
    # the reference raises on one, which `verify` reports. Both raise on
    # `inf / inf`, which would be NaN (#257).
    t = ibis.table({"a": "float64", "b": "float64"}, name="t")
    duck = sv.sql("SELECT a / b AS ratio FROM t", dialect="duckdb", t=t)
    ref = sv.sql("SELECT a / b AS ratio FROM t", dialect="duckdb", semantics="reference", t=t)
    assert [i.kind for i in sv.verify(duck).issues] == ["domain error"]
    assert any("zero" in str(i) for i in sv.verify(ref).issues)


def test_sql_checks_dialect_and_semantics():
    t = ibis.table({"a": "int64"}, name="t")
    with pytest.raises(ValueError, match="dialect must be 'duckdb'"):
        sv.sql("SELECT a FROM t", dialect="postgres", t=t)
    with pytest.raises(ValueError, match="semantics must be"):
        sv.sql("SELECT a FROM t", dialect="duckdb", semantics="spark", t=t)
    with pytest.raises(Unsupported, match="unknown function"):
        sv.sql("SELECT my_udf(a) FROM t", dialect="duckdb", t=t)


def test_sql_is_duckdbs_by_default():
    t = ibis.table({"a": "int64"}, name="t")
    op: Any = sv.sql("SELECT a FROM t", t=t).op()
    assert (op.dialect, op.semantics) == ("duckdb", "duckdb")


@pytest.mark.skipif(
    not (catalogue.ROOT / "schemas.toml").is_file(),
    reason="catalogue/ of the repository is not here",
)
def test_benchmark_queries_through_the_lift():
    # The #229 score (`python -m sverify_dev.lift`), on SSB's four queries.
    results = score(["ssb"])
    assert len(results) == 4
    assert all(c.ok for c in results.values()), results


def test_a_remainder_of_doubles_runs_with_the_reference_semantics():
    # `sverify_fmod` (#256): C's `fmod`, as DuckDB computes `%` of doubles.
    result = check(
        "SELECT id, price % 2.0 AS m, -price % 4.0 AS n FROM orders", TABLES, "reference"
    )
    assert result.ok, f"{result.stage}: {result.detail}"


@pytest.mark.parametrize(
    "query",
    [
        # NaN by zero and of an infinity, as DuckDB computes them.
        "SELECT id, price % 0 AS z, price % qty AS m, 7.5 % price AS r FROM orders",
        "SELECT id, (price / 0) % 2 AS i, (price / 0) / (price / 0) AS n FROM orders",
        # `log` of 0 is -inf, of a negative NaN.
        "SELECT id, log(price) AS l, log(qty - 3) AS lq, sign(price) AS s, sign(qty) AS sq"
        " FROM orders",
        # `avg` of integers: the exact sum by the count, in doubles.
        "SELECT customer, avg(amount) AS a, avg(qty) AS q, avg(DISTINCT qty) AS d"
        " FROM orders GROUP BY customer",
        "SELECT id, avg(amount) OVER (PARTITION BY customer) AS a FROM orders",
        "SELECT id, greatest(price, -price, 0.5) AS g, least(amount, id) AS l FROM orders",
    ],
)
def test_the_generated_lift_is_duckdbs_with_nan_and_infinities(query):
    # With DuckDB's semantics, these come from Lean's generated lift table
    # (#268), which states NaN and ±inf exactly instead of refusing them.
    result = check(query, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


def test_nested_values_have_no_order_yet():
    # DuckDB orders structs field by field; the model's order differs.
    schema = {"t": ibis.schema({"s": "struct<p: int64, q: int64>"})}
    with pytest.raises(Refused, match="ordering comparisons"):
        lift("SELECT a.s < b.s AS c FROM t AS a, t AS b", schema)


def test_constants_out_of_range_are_cast_not_folded():
    # `200::TINYINT` raises in DuckDB: the plan casts, it doesn't hold an
    # INT8 literal of 200.
    plan = lift("SELECT 200::TINYINT AS x, 100::TINYINT AS y", {}).plan
    exprs = plan["relations"][0]["root"]["input"]["project"]["expressions"]
    assert "cast" in exprs[0] and exprs[1] == {"literal": {"i8": 100}}


def test_digit_separators_are_read_as_duckdb_reads_them():
    result = check("SELECT 1_000 AS a, 1_000.5 AS b, 2_5e1 AS c", {})
    assert result.ok, f"{result.stage}: {result.detail}"


def test_greatest_and_least_of_many_values_check_fast():
    # #340: GREATEST/LEAST were read as a conditional that copies its first
    # argument at each step, so checking 10 of them ran for minutes. As one
    # operation per pair, 30 check at once and agree with DuckDB.
    import time

    args = ", ".join(f"amount + {i}" for i in range(30))
    query = f"SELECT id, LEAST({args}) AS lo, GREATEST({args}, qty) AS hi FROM orders"
    start = time.monotonic()
    result = check(query, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"
    assert time.monotonic() - start < 30


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


# #348: list literals, indexing and UNNEST in DuckDB's SQL. Lean's rows match
# DuckDB's (oracle A), and so do DuckDB's running the plan Lean writes (oracle
# C, #94).
LISTS = ibis.schema({"a": "int64", "l": "array<int64>"})
LIST_ROWS = [(1, [1, 2, 3]), (2, []), (3, None), (4, [5, None]), (None, [7])]
LIST_QUERIES = [
    "SELECT [1, 2, 3] AS x",
    "SELECT [[1], [2, 3]] AS x",
    "SELECT [1, NULL] AS x",
    "SELECT [10, 20, 30][2] AS x",
    "SELECT a, l[1] AS f, l[-1] AS z, l[0] AS n, l[3] AS t3, l[-3] AS m FROM t",
    "SELECT a, UNNEST(l) AS e FROM t",
    "SELECT UNNEST([1, 2, 3]) AS e",
    "SELECT a, UNNEST(l) + 1 AS e FROM t WHERE a > 1",
    # The same UNNEST twice is one (DuckDB zips equal lists).
    "SELECT UNNEST(l) AS x, UNNEST(l) * 10 AS y FROM t",
]


@pytest.mark.parametrize("sql", LIST_QUERIES)
def test_lists_lift_as_duckdb_reads_them(sql):
    from sverify.engine import connect, put_table, run_plan, written_plan
    from sverify.testing import duckdb_sql, inline_tables, lean_values

    con = connect()
    put_table(
        con,
        "t",
        pa.table(
            {
                "a": pa.array([r[0] for r in LIST_ROWS], pa.int64()),
                "l": pa.array([r[1] for r in LIST_ROWS], pa.list_(pa.int64())),
            }
        ),
    )
    plan = json.dumps(lift(sql, {"t": LISTS}, "duckdb").plan)
    lean = lean_values(json.dumps(inline_tables(json.loads(plan), {"t": LIST_ROWS})))
    want = [tuple(r.values()) for r in duckdb_sql(con, sql).to_pylist()]
    assert sorted(map(repr, lean)) == sorted(map(repr, want))
    got = [tuple(r.values()) for r in run_plan(con, written_plan(plan), "duckdb").to_pylist()]
    assert sorted(map(repr, got)) == sorted(map(repr, want))


@pytest.mark.parametrize(
    ("sql", "why"),
    [
        ("SELECT [] AS x", "empty list literal"),
        ("SELECT [a, 1] AS x FROM t", "computed elements"),
        ("SELECT l[1:2] AS x FROM t", "slices"),
        ("SELECT l[a] AS x FROM t", "constant index"),
        ("SELECT [1, 2.5] AS x", "decimal"),
        ("SELECT UNNEST(l) AS x, UNNEST([1, 2]) AS y FROM t", "more than one UNNEST"),
        ("SELECT 'abc'[1] AS x", "indexing a string"),
    ],
)
def test_list_refusals_say_why(sql, why):
    with pytest.raises(Refused, match=why):
        lift(sql, {"t": LISTS}, "duckdb")


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
    """SQLGlot does not parse DuckDB's `TABLE t` (upstream/LEDGER.md, SG-6)."""
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

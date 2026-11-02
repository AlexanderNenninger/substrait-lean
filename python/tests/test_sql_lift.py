"""DuckDB SQL through sverify's own lift (`sverify.sql_lift`, #239):
`sv.sql(query, dialect="duckdb", semantics=...)`, its two profiles, its
refusals, and oracles A and C (`sverify_dev.lift`)."""

import datetime as dt
import json
from decimal import Decimal

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from _pipelines import arrow_table as table
from _pipelines import rows
from sverify.engine import run_checker
from sverify.engines import Unsupported
from sverify.errors import VerificationError
from sverify.io import StaticSource
from sverify.plan_json import Unsupported as Refused
from sverify.sql_lift import DUCKDB, REFERENCE, lift
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
    ]
)
CUSTOMERS = pa.schema([pa.field("name", pa.string()), pa.field("region", pa.string())])

ORDER_ROWS = [
    (1, "ada", 5, 3, 2.5, Decimal("10.50"), dt.date(2024, 1, 1)),
    (2, "bob", 7, None, 0.0, Decimal("3.25"), dt.date(2024, 1, 2)),
    (3, "ada", 0, 4, -1.5, None, dt.date(2024, 2, 1)),
    (4, "cy", 9, 2, None, Decimal("0.01"), None),
    (5, None, 2, 7, 10.0, Decimal("99.99"), dt.date(2023, 12, 31)),
]
CUSTOMER_ROWS = [("ada", "eu"), ("bob", "us"), ("dan", "eu")]
TABLES = {"orders": table(ORDERS, ORDER_ROWS), "customers": table(CUSTOMERS, CUSTOMER_ROWS)}
SCHEMAS = {n: ibis.Schema.from_pyarrow(t.schema) for n, t in TABLES.items()}

#: Queries of the subset, each through oracles A and C.
QUERIES = [
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
    "SELECT id, amount / 0 AS inf, price / 0 AS p FROM orders",
    pytest.param(
        "SELECT 7 / 2 AS h",
        marks=pytest.mark.xfail(
            strict=True,
            reason="oracle C: the written plan's IEEE division of two double literals "
            "reads them as integer codes (#96)",
        ),
    ),
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
        "float_division_by_zero",
        "float_to_int",
        "decimal_to_int",
        "float_modulus_by_zero",
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
        ("SELECT id FROM orders UNION ALL SELECT id FROM orders", "Union is not supported"),
        ("WITH t AS (SELECT id FROM orders) SELECT id FROM t", "CTEs"),
        ("SELECT sum(id) OVER () FROM orders", "window functions"),
        ("SELECT nope FROM orders", "cannot resolve"),
        ("SELECT id FROM elsewhere", "cannot resolve"),
        ("SELECT id, customer FROM orders GROUP BY id", "GROUP BY"),
        ("SELECT avg(cost) FROM orders", "avg of a DECIMAL"),
        ("SELECT * FROM orders o JOIN orders p ON o.id = p.id", "two output columns named id"),
        ("SELECT id FROM orders o FULL JOIN customers c ON o.customer = c.name", "FULL"),
        ("SELECT TRY_CAST(id AS INT) FROM orders", "TRY_CAST"),
        ("SELECT id FROM orders LIMIT qty", "LIMIT"),
        ("SELECT 170141183460469231731687303715884105727 AS h", "HUGEINT"),
        ("SELEC id FROM orders", "cannot parse"),
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
    # DuckDB's `/` by zero is inf, so `ratio` is never an error there; the
    # reference raises on a zero divisor, which `verify` reports.
    t = ibis.table({"a": "float64", "b": "float64"}, name="t")
    duck = sv.sql("SELECT a / b AS ratio FROM t", dialect="duckdb", t=t)
    ref = sv.sql("SELECT a / b AS ratio FROM t", dialect="duckdb", semantics="reference", t=t)
    assert not sv.verify(duck).issues
    assert any("zero" in str(i) for i in sv.verify(ref).issues)


def test_sql_checks_dialect_and_semantics():
    t = ibis.table({"a": "int64"}, name="t")
    with pytest.raises(ValueError, match="dialect must be 'duckdb'"):
        sv.sql("SELECT a FROM t", dialect="postgres", t=t)
    with pytest.raises(ValueError, match="semantics must be"):
        sv.sql("SELECT a FROM t", dialect="duckdb", semantics="spark", t=t)
    with pytest.raises(ValueError, match="needs a dialect"):
        sv.sql("SELECT a FROM t", semantics="duckdb", t=t)
    with pytest.raises(Unsupported, match="unknown function"):
        sv.sql("SELECT my_udf(a) FROM t", dialect="duckdb", t=t)


def test_without_a_dialect_sql_stays_datafusions():
    t = ibis.table({"a": "int64"}, name="t")
    op = sv.sql("SELECT a FROM t", t=t).op()
    assert op.dialect is None and op.semantics is None


def test_benchmark_queries_through_the_lift():
    # The #229 score (`python -m sverify_dev.lift`), on SSB's four queries.
    results = score(["ssb"])
    assert len(results) == 4
    assert all(c.ok for c in results.values()), results

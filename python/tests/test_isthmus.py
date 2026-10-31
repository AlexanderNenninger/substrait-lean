"""Isthmus as the SQL producer (`connect(sql_producer="isthmus")`).

The tests that compile SQL need the Isthmus binary (`$SVERIFY_ISTHMUS`, or
`isthmus` on `PATH`) and are skipped without it; CI downloads a pinned
release. Each query here is standard SQL that DataFusion and Calcite both
read: both plans must verify and run on DuckDB to DataFusion's own result.
"""

import datetime as dt
from decimal import Decimal

import pyarrow as pa
import pytest

import sverify as sv
from sverify.engine import (
    create_statements,
    default_sql_producer,
    isthmus_json,
    isthmus_path,
    plan_json,
    run_checker,
    run_plan,
    run_sql,
    substrait_json,
    written_plan,
)
from sverify.errors import SqlError
from sverify.incremental import IncrementalView, arrow_rows
from sverify.testing import canonical

needs_isthmus = pytest.mark.skipif(isthmus_path() is None, reason="no Isthmus binary")

T0 = dt.datetime(2024, 1, 1)
ORDERS = pa.table(
    {
        "id": pa.array([1, 2, 3, 4, 5], pa.int64()),
        "customer": ["ada", "bob", "ada", None, "cy"],
        "amount": [30.0, 5.5, None, 12.0, 7.25],
        "qty": pa.array([3, 1, 2, None, 4], pa.int64()),
        "ts": pa.array(
            [T0 + dt.timedelta(hours=h) for h in (0, 5, 30, 49, 50)], pa.timestamp("us")
        ),
        "paid": [True, False, None, True, False],
    },
    schema=pa.schema(
        [
            pa.field("id", pa.int64(), nullable=False),
            ("customer", pa.string()),
            ("amount", pa.float64()),
            ("qty", pa.int64()),
            ("ts", pa.timestamp("us")),
            ("paid", pa.bool_()),
        ]
    ),
)
CUSTOMERS = pa.table({"name": ["ada", "bob", "dee"], "city": ["Paris", "Rome", "Oslo"]})


@pytest.fixture
def con():
    con = sv.connect(sql_producer="isthmus")
    con.put("orders", ORDERS)
    con.put("customers", CUSTOMERS)
    return con


#: Standard SQL that DataFusion and Calcite both read.
AGREE = {
    "filter_project": "SELECT id, amount * 2 AS a, qty + 1 AS q FROM orders WHERE amount > 6",
    "join": (
        "SELECT o.id, c.city FROM orders o JOIN customers c ON o.customer = c.name WHERE o.qty >= 2"
    ),
    "left_join": "SELECT o.id, c.city FROM orders o LEFT JOIN customers c ON o.customer = c.name",
    "aggregate": (
        "SELECT customer, COUNT(*) AS n, SUM(qty) AS s, MIN(ts) AS first_ts "
        "FROM orders GROUP BY customer"
    ),
    "case_strings": (
        "SELECT id, CASE WHEN qty > 2 THEN 'big' WHEN qty > 1 THEN 'mid' ELSE 'small' END AS size "
        "FROM orders"
    ),
    "string_functions": (
        "SELECT UPPER(customer) AS u, CHAR_LENGTH(customer) AS n, customer || '!' AS e "
        "FROM orders WHERE customer LIKE 'a%'"
    ),
    "timestamp_literal": "SELECT id FROM orders WHERE ts >= TIMESTAMP '2024-01-02 00:00:00'",
    # Calcite types `DATE + INTERVAL` as a timestamp, under a cast to DATE.
    "date_arithmetic": (
        "SELECT id, CAST(ts AS DATE) + INTERVAL '1' DAY AS a,"
        " CAST(ts AS DATE) + INTERVAL '1' MONTH AS b FROM orders"
    ),
    "in_list": "SELECT id FROM orders WHERE customer IN ('ada', 'cy') OR qty IN (1)",
    "is_true": "SELECT id, paid IS TRUE AS p, paid IS NOT FALSE AS q FROM orders",
    "coalesce": "SELECT id, COALESCE(qty, 0) AS q, NULLIF(customer, 'ada') AS c FROM orders",
    "union_all": "SELECT id FROM orders WHERE qty > 2 UNION ALL SELECT id FROM orders WHERE id < 2",
    "distinct": "SELECT DISTINCT customer FROM orders",
    "in_subquery": "SELECT id FROM orders WHERE customer IN (SELECT name FROM customers)",
    "row_number": (
        "SELECT id, ROW_NUMBER() OVER (PARTITION BY customer ORDER BY id) AS rn FROM orders"
    ),
    "nested_window": (
        "SELECT id, ROW_NUMBER() OVER (ORDER BY id) - 1 AS rn0, "
        "qty - LAG(qty) OVER (ORDER BY id) AS dq FROM orders"
    ),
    "order_limit": "SELECT id, qty FROM orders ORDER BY id DESC LIMIT 3",
}


def checked(plan: str) -> str:
    code, out, err = run_checker((), plan)
    assert code == 0, (out + err).strip().splitlines()[-3:]
    return written_plan(plan)


def rows(table: pa.Table) -> list[str]:
    # DataFusion types `ROW_NUMBER() - 1` as a decimal.
    def norm(v: object) -> object:
        return int(v) if isinstance(v, Decimal) and v == v.to_integral_value() else v

    return canonical(tuple(map(norm, r)) for r in arrow_rows(table))


@needs_isthmus
@pytest.mark.parametrize("name", sorted(AGREE))
def test_isthmus_agrees_with_datafusion(con, name):
    sql = AGREE[name]
    reference = rows(run_sql(con, sql))
    assert rows(run_plan(con, checked(isthmus_json(con, sql)), "duckdb")) == reference
    assert rows(run_plan(con, checked(substrait_json(con, sql)), "duckdb")) == reference


@needs_isthmus
@pytest.mark.parametrize(
    ("sql", "error"),
    [
        # Calcite types `'ab '` as CHAR(3): its trailing blank is padding.
        ("SELECT CHAR_LENGTH('ab ') AS n FROM orders", "trailing blanks"),
    ],
)
def test_isthmus_plans_lean_refuses(con, sql, error):
    code, out, err = run_checker((), isthmus_json(con, sql))
    assert code != 0
    assert error in out + err


@needs_isthmus
def test_isthmus_folds_hours_added_to_a_date(con):
    """Calcite drops the hour of `DATE + INTERVAL '1' HOUR` (zero days), so
    Lean accepts Isthmus' plan and gives the date, as DataFusion does; through
    DataFusion's own plan, which keeps the hour, the checker refuses it."""
    sql = "SELECT id, CAST(ts AS DATE) AS d, CAST(ts AS DATE) + INTERVAL '1' HOUR AS e FROM orders"
    out = run_plan(con, checked(isthmus_json(con, sql)), "duckdb")
    assert all(r["d"] == r["e"] for r in out.to_pylist())
    assert rows(run_sql(con, sql)) == rows(out)
    code, out, err = run_checker((), substrait_json(con, sql))
    assert code != 0 and "a part of a day" in out + err


@needs_isthmus
def test_isthmus_errors(con):
    with pytest.raises(SqlError, match="not found"):
        plan_json(con, "SELECT nope FROM orders")


@needs_isthmus
def test_incremental_view_from_sql(con):
    view = IncrementalView(con, "SELECT id, qty * 2 AS q FROM orders WHERE qty > 1", "v")
    view.apply({"orders": sv.Changes(inserts=[(6, "dee", 1.0, 9, T0, True)])})
    assert canonical(view.rows()) == canonical(view.recompute())
    assert (6, 18) in view.rows()


def test_create_statements_quote_identifiers():
    con = sv.connect()
    con.put('we"ird', pa.table({"Col A": pa.array([1], pa.int32()), "d": [dt.date(2024, 1, 1)]}))
    con.put("tz", pa.table({"t": pa.array([0], pa.timestamp("us", tz="UTC"))}))
    con.put("orders", ORDERS)
    ddl, skipped = create_statements(con)
    assert ddl[0] == 'CREATE TABLE "we""ird" ("Col A" INTEGER, "d" DATE)'
    assert ddl[1].startswith('CREATE TABLE "orders" ("id" BIGINT NOT NULL, "customer" VARCHAR')
    assert '"ts" TIMESTAMP(6)' in ddl[1]
    assert skipped == ["tz (t: timestamp[us, tz=UTC])"]


def test_sql_producer_choice(monkeypatch):
    with pytest.raises(ValueError, match="unknown SQL producer"):
        sv.connect(sql_producer="calcite")  # pyrefly: ignore[bad-argument-type]
    monkeypatch.setattr(sv.engine, "has_datafusion", lambda: False)
    monkeypatch.setattr(sv.engine, "isthmus_path", lambda: "/bin/isthmus")
    assert default_sql_producer() == "isthmus"
    monkeypatch.setattr(sv.engine, "isthmus_path", lambda: None)
    with pytest.raises(ImportError, match=r"sverify\[datafusion\].*Isthmus"):
        plan_json(sv.connect(), "SELECT 1")
    with pytest.raises(ImportError, match="Isthmus binary"):
        plan_json(sv.connect(sql_producer="isthmus"), "SELECT 1")


@needs_isthmus
def test_without_datafusion_isthmus_plans_sql_models(monkeypatch):
    """`sverify.sql` falls back to Isthmus for its schema and plan."""
    from test_sql_models import paid, per_customer, rows, sources

    monkeypatch.setattr("sverify.engine.has_datafusion", lambda: False)
    orders, _customers = sources()
    node = per_customer(paid(orders))
    node.refresh()
    assert rows(node) == [("ada", 5), ("bob", 7)]

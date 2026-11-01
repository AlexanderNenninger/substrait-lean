"""`.pipe`: nodes composed left to right, in the order the data flows, with
transforms, SQL steps and plain functions as steps."""

from typing import assert_type

import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from _pipelines import arrow_table as table
from _pipelines import paid_nonzero as paid
from _pipelines import rows
from sverify.errors import CompositionError
from sverify.io import DeltaSink, StaticSource

ORDERS = pa.schema(
    [
        pa.field("id", pa.int64(), nullable=False),
        pa.field("cid", pa.string()),
        pa.field("amount", pa.int64(), nullable=False),
    ]
)
CUSTOMERS = pa.schema([pa.field("cid", pa.string()), pa.field("region", pa.string())])
REGIONS = pa.schema([pa.field("region", pa.string()), pa.field("manager", pa.string())])


def sources():
    orders = StaticSource(
        table(ORDERS, [(1, "ada", 30), (2, "bob", 0), (3, "ada", 7)]), name="orders"
    )
    customers = StaticSource(table(CUSTOMERS, [("ada", "eu"), ("bob", "us")]), name="customers")
    regions = StaticSource(table(REGIONS, [("eu", "eve"), ("us", "uma")]), name="regions")
    return orders, customers, regions


@sv.transform(requires={"t": [_.amount > 0]}, ensures=[_.doubled > 0])
def doubled(t):
    return t.select(t.id, doubled=t.amount * 2)


@sv.transform(requires={"orders": [_.amount > 0]})
def enrich(orders, customers):
    return orders.join(customers, "cid").select(orders.id, customers.region)


@sv.transform()
def daily_totals(t):
    return t.group_by("cid").aggregate(total=t.amount.sum())


# -- chaining -------------------------------------------------------------------


def test_pipe_chains_left_to_right():
    orders, _c, _r = sources()
    node = orders.pipe(paid).pipe(doubled)
    assert_type(node, sv.Node)
    assert isinstance(node, sv.Node)
    assert node.name == "doubled"
    node.refresh()
    assert rows(node) == [(1, 60), (3, 14)]


def test_pipe_gives_the_same_plan_as_the_call_form():
    orders, customers, _r = sources()
    assert orders.pipe(paid).pipe(doubled).plan == doubled(paid(orders)).plan
    assert (
        orders.pipe(paid).pipe(enrich, customers=customers).plan
        == enrich(paid(orders), customers=customers).plan
    )


def test_pipe_checks_the_contract_like_the_call_form():
    orders, _c, _r = sources()

    # doubled needs amount > 0: paid guarantees it, `big` doesn't.
    @sv.transform(ensures=[_.amount >= 0])
    def big(t):
        return t.filter(t.amount > -1)

    with pytest.raises(CompositionError) as piped:
        orders.pipe(big).pipe(doubled)
    with pytest.raises(CompositionError) as called:
        doubled(big(orders))
    assert str(piped.value) == str(called.value)
    orders.pipe(paid).pipe(doubled)


def test_pipe_on_a_node_and_on_a_stored_node(tmp_path):
    orders, _c, _r = sources()
    stored = orders.pipe(paid).write(DeltaSink(str(tmp_path / "paid")))
    node = stored.pipe(doubled)
    node.refresh()
    assert rows(node) == [(1, 60), (3, 14)]


# -- fan-in and fan-out ---------------------------------------------------------


def test_fan_in_by_keyword():
    orders, customers, _r = sources()
    node = orders.pipe(paid).pipe(enrich, customers=customers)
    node.refresh()
    assert rows(node) == [(1, "eu"), (3, "eu")]


def test_fan_out_with_a_group(tmp_path):
    orders, customers, _r = sources()
    paid_orders = orders.pipe(paid).write(DeltaSink(str(tmp_path / "paid")))
    daily = paid_orders.pipe(daily_totals).write(DeltaSink(str(tmp_path / "daily")))
    enriched = paid_orders.pipe(enrich, customers=customers)
    result = sv.group(daily, enriched).refresh()
    assert [s.node for s in result.nodes] == ["paid", "daily", "enrich"]
    assert len(result.writes) == 2  # paid once, daily once
    assert rows(daily) == [("ada", 37)]
    assert rows(enriched) == [(1, "eu"), (3, "eu")]


def test_missing_duplicate_and_unknown_inputs_name_the_parameters():
    orders, customers, _r = sources()
    with pytest.raises(TypeError, match=r"enrich\(orders, customers\).*customers"):
        orders.pipe(enrich)
    with pytest.raises(TypeError, match=r"enrich\(orders, customers\): 'orders' is given twice"):
        orders.pipe(enrich, orders=orders, customers=customers)
    with pytest.raises(TypeError, match=r"enrich\(orders, customers\).*regions"):
        orders.pipe(enrich, customers=customers, regions=customers)


def test_pipe_takes_steps_only():
    orders, customers, _r = sources()
    with pytest.raises(TypeError, match="pipe takes a step"):
        orders.pipe(customers)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="pipe takes a step"):
        orders.pipe("SELECT * FROM orders")  # type: ignore[arg-type]


# -- plain functions ------------------------------------------------------------


def test_a_plain_function_is_a_transform_without_a_contract():
    orders, customers, _r = sources()
    quick = orders.pipe(lambda t: t.filter(_.amount > 5))
    assert quick.name == "step"
    quick.refresh()
    assert rows(quick) == [(1, "ada", 30), (3, "ada", 7)]

    def regional(orders, customers):
        return orders.join(customers, "cid").select(orders.id, customers.region)

    node = orders.pipe(regional, customers=customers)
    assert node.name == "regional"
    assert node.plan == sv.transform()(regional)(orders, customers=customers).plan
    # Downstream transforms may assume nothing a plain function didn't prove.
    with pytest.raises(CompositionError):
        orders.pipe(lambda t: t).pipe(doubled)


# -- SQL steps ------------------------------------------------------------------

JOIN = "SELECT o.id, c.region FROM customers c JOIN orders o ON o.cid = c.cid"


def test_sql_step_binds_the_chained_node_by_elimination():
    orders, customers, _r = sources()
    step = sv.sql(JOIN)
    assert step.tables == ["customers", "orders"]
    node = orders.pipe(paid).pipe(step, customers=customers)
    node.refresh()
    assert rows(node) == [(1, "eu"), (3, "eu")]
    # The chained node is orders, wherever the query reads it.
    flipped = customers.pipe(sv.sql(JOIN), orders=orders.pipe(paid))
    flipped.refresh()
    assert rows(flipped) == rows(node)


def test_sql_step_with_a_matching_as():
    orders, customers, regions = sources()
    query = """
        SELECT o.id, c.region, r.manager
        FROM customers c
        JOIN orders o ON o.cid = c.cid
        JOIN regions r ON r.region = c.region
    """
    node = orders.pipe(paid).pipe(sv.sql(query, as_="orders"), customers=customers, regions=regions)
    node.refresh()
    assert rows(node) == [(1, "eu", "eve"), (3, "eu", "eve")]


def test_sql_step_with_a_wrong_as_names_both():
    orders, customers, _r = sources()
    with pytest.raises(TypeError, match=r"as_='orders'.*left over.*'customers'"):
        customers.pipe(sv.sql(JOIN, as_="orders"), orders=orders)
    with pytest.raises(TypeError, match=r"as_='customers'.*left over.*'orders'"):
        orders.pipe(sv.sql(JOIN, as_="customers"), customers=customers)
    with pytest.raises(TypeError, match=r"as_='nope' is not a table the query reads"):
        sv.sql(JOIN, as_="nope")


def test_sql_step_tables_with_no_input():
    orders, customers, _r = sources()
    query = (
        "SELECT o.id, r.manager FROM orders o JOIN customers c ON o.cid = c.cid "
        "JOIN regions r ON r.region = c.region"
    )
    with pytest.raises(TypeError, match="the tables orders, customers, regions have no input"):
        orders.pipe(sv.sql(query))
    with pytest.raises(TypeError, match="the tables orders, regions have no input"):
        orders.pipe(sv.sql(query), customers=customers)


def test_sql_step_with_the_chained_node_unused_or_an_unknown_keyword():
    orders, customers, _r = sources()
    with pytest.raises(TypeError, match="chained node is unused"):
        orders.pipe(sv.sql(JOIN), orders=orders, customers=customers)
    with pytest.raises(TypeError, match="reads no table 'regions'; it reads customers, orders"):
        orders.pipe(sv.sql(JOIN), customers=customers, regions=customers)


def test_sql_step_tables_skip_ctes_and_repeats():
    step = sv.sql(
        "WITH big AS (SELECT * FROM orders WHERE amount > 5) "
        "SELECT a.id FROM big a JOIN Orders b ON a.id = b.id"
    )
    assert step.tables == ["orders"]
    orders, _c, _r = sources()
    node = orders.pipe(step)
    node.refresh()
    assert rows(node) == [(1,), (3,)]


def test_sql_step_called_directly_takes_tables_by_keyword():
    orders, customers, _r = sources()
    node = sv.sql(JOIN)(orders=orders, customers=customers)
    assert node.plan == orders.pipe(sv.sql(JOIN), customers=customers).plan


def test_sql_with_tables_is_still_an_ibis_table():
    con = sv.connect()
    con.put("orders", table(ORDERS, [(1, "ada", 30)]))
    expr = sv.sql("SELECT id FROM orders", orders=con.table("orders"))
    assert not isinstance(expr, sv.Node)
    with pytest.raises(TypeError, match="as_ names the chained node"):
        sv.sql("SELECT id FROM orders", as_="orders", orders=con.table("orders"))

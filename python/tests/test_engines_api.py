"""`sverify.engines` before 1.0 (api-review F1, F3, F4): `Report.to_sql`,
`Node.to_sql`, `Connection.create` and `rows`, and the deprecated names."""

import duckdb
import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify.engines import substrait_json, to_sql, written_plan
from sverify.errors import RouteError, UnverifiedRunError
from sverify.io import StaticSource
from sverify.sql import dialect_of

SCHEMA = ibis.schema({"id": "int64", "amount": "int64"})


def _con() -> sv.engines.Connection:
    con = sv.connect()
    con.create("orders", SCHEMA, [(1, 30), (2, 5)])
    return con


def _report(**kw):
    con = _con()
    return sv.verify(
        "SELECT id, amount FROM orders WHERE amount > 10",
        tables={"orders": con.table("orders")},
        **kw,
    )


def test_report_to_sql_is_what_run_runs():
    report = _report()
    sql = report.to_sql()
    assert report.internal_plan is not None
    assert sql == to_sql(written_plan(report.internal_plan), "duckdb")
    db = duckdb.connect()
    db.register("orders", pa.table({"id": [1, 2], "amount": [30, 5]}))
    assert db.sql(sql).fetchall() == [(1, 30)]


@pytest.mark.parametrize("name", ["snowflake", "spark"])
def test_report_to_sql_takes_a_name_or_a_dialect(name):
    report = _report()
    assert report.to_sql(name) == report.to_sql(dialect_of(name))


def test_report_to_sql_refuses_an_unknown_dialect():
    with pytest.raises(ValueError, match="unknown dialect 'oracle'"):
        _report().to_sql("oracle")


def test_report_to_sql_refuses_what_is_not_proved():
    report = _report(ensures=[_.amount > 50])
    assert not report.proved
    with pytest.raises(UnverifiedRunError) as e:
        report.to_sql("snowflake")
    assert "unverified=True" not in str(e.value)


def test_report_to_sql_writes_engine_semantics_only_for_its_engine():
    report = _report(semantics="duckdb")
    assert report.proved
    assert "SELECT" in report.to_sql("duckdb")
    with pytest.raises(RouteError, match="only for plans verified under the reference"):
        report.to_sql("snowflake")


def test_report_to_sql_needs_a_plan():
    with pytest.raises(ValueError, match="no plan"):
        sv.Report(requires={}, ensures=[]).to_sql()


def test_node_to_sql_is_the_stage_refresh_runs():
    orders = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders")

    @sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.amount > 10])
    def big(orders):
        return orders.filter(orders.amount > 10)

    node = orders.pipe(big)
    assert node.to_sql() == to_sql(node.internal_plan, "duckdb")
    assert node.to_sql("spark") == to_sql(node.internal_plan, "spark")
    node.refresh()
    assert node.to_arrow().to_pylist() == [{"id": 1, "amount": 30}]


def test_node_to_sql_refuses_an_unproved_contract():
    orders = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders")

    @sv.transform(ensures=[_.amount > 50], on_unproved="warn")
    def big(orders):
        return orders.filter(orders.amount > 10)

    with pytest.warns(UserWarning):
        node = orders.pipe(big)
    with pytest.raises(UnverifiedRunError):
        node.to_sql()


def test_connection_create_and_rows():
    con = sv.connect()
    con.create("t", pa.schema([pa.field("x", pa.int64(), nullable=False)]), [(1,), (2,)])
    assert con.rows("t") == [(1,), (2,)]
    assert con.get("t").schema.field("x").nullable is False
    con.create("t", SCHEMA)
    assert con.rows("t") == []
    with pytest.raises(KeyError):
        con.rows("missing")


def test_create_table_and_table_rows_are_deprecated():
    from sverify.engines import create_table, table_rows

    con = sv.connect()
    with pytest.warns(DeprecationWarning, match=r"con\.create\(name, schema, rows\)"):
        create_table(con, "t", SCHEMA, [(1, 2)])
    with pytest.warns(DeprecationWarning, match=r"con\.rows\(name\)"):
        assert table_rows(con, "t") == [(1, 2)]


def test_connection_arrow_and_ibis_are_deprecated():
    con = _con()
    with pytest.warns(DeprecationWarning, match=r"con\.get\(name\)"):
        assert con.arrow["orders"].num_rows == 2
    with pytest.warns(DeprecationWarning, match=r"get_backend\(\)"):
        backend = con.ibis
    assert backend is con.table("orders").get_backend()


def test_substrait_json_defaults_to_the_reference():
    con = _con()
    sql = "SELECT id // 2 AS h FROM orders"
    assert substrait_json(con, sql) == substrait_json(con, sql, "reference")


def test_rows_and_tables_column_by_column():
    from sverify.engine import arrow_rows, to_arrow

    schema = pa.schema([pa.field("a", pa.int64()), pa.field("b", pa.string())])
    rows = [(1, "x"), (None, None), (3, "z")]
    table = to_arrow(iter(rows), schema)
    assert table.to_pylist() == [{"a": a, "b": b} for a, b in rows]
    assert arrow_rows(table) == rows
    assert to_arrow([], schema).num_rows == 0 and arrow_rows(to_arrow([], schema)) == []
    assert arrow_rows(pa.table({"a": [1, 2]}).select([])) == [(), ()]
    with pytest.raises(ValueError, match="2 values"):
        to_arrow([(1, "x"), (2,)], schema)

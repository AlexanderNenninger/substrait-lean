"""`sverify` works without DataFusion, which is an optional extra.

Each test runs a script in a fresh interpreter where importing `datafusion`
fails, as if the package were not installed: incremental views, pipelines and
contracts on DuckDB (the default) and Polars, and a clear error for what does
need DataFusion (its engine, and SQL strings).
"""

import subprocess
import sys
import textwrap

import pytest

PRELUDE = """
import importlib.abc
import sys

import ibis
from ibis import _


class NoDataFusion(importlib.abc.MetaPathFinder):
    def find_spec(self, name, path=None, target=None):
        if name.split(".")[0] == "datafusion":
            raise ImportError(f"No module named {name!r} (blocked by the test)")
        return None


sys.meta_path.insert(0, NoDataFusion())

import sverify as sv

con = sv.connect(ENGINE)
sv.create_table(
    con,
    "orders",
    ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
    [(1, "ada", 30), (2, "bob", 5)],
)
sv.create_table(
    con, "customers", ibis.schema({"name": "string", "city": "string"}), [("ada", "Paris")]
)
orders, customers = con.table("orders"), con.table("customers")
"""


def run(script: str, engine: str = "duckdb") -> None:
    code = PRELUDE.replace("ENGINE", repr(engine)) + textwrap.dedent(script)
    out = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True)
    assert out.returncode == 0, out.stderr


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_views_and_pipelines(engine):
    run(
        """
        big = (
            orders.filter(orders.amount > 10)
            .join(customers, orders.customer == customers.name)
            .select(orders.id, customers.city, orders.amount)
        )
        view = sv.IncrementalView(con, big, "big_orders")
        view.apply(
            {
                "orders": sv.Changes(inserts=[(3, "bob", 50)], deletes=[(1, "ada", 30)]),
                "customers": sv.Changes(inserts=[("bob", "Rome")]),
            }
        )
        assert view.rows() == view.recompute() == [(3, "Rome", 50)]
        assert con.table("big_orders").to_pyarrow().num_rows == 1

        pipe = sv.Pipeline(con)
        totals = pipe.view("totals", orders.group_by("customer").aggregate(s=_.amount.sum()))
        pipe.apply({"orders": sv.Changes(inserts=[(4, "ada", 1)])})
        assert totals.rows() == totals.recompute()
        assert "datafusion" not in sys.modules
        """,
        engine,
    )


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_contracts(engine):
    run(
        """
        @sv.transform(
            requires={"orders": [_.amount >= 0, _.id.notnull()]},
            ensures=[_.doubled >= 0],
        )
        def doubled(orders):
            return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)

        assert doubled(orders).to_pyarrow().to_pylist() == [{"id": 1, "doubled": 60}]
        checked_on_engine = sv.transform(
            requires={"orders": [_.amount >= 0]}, engine=con.engine
        )(lambda orders: orders)
        checked_on_engine(orders)
        sv.create_table(con, "bad", orders.schema(), [(1, "ada", -1)])
        try:
            checked_on_engine(con.table("bad"))
        except sv.PreconditionError:
            pass
        else:
            raise AssertionError("the precondition was not checked")
        assert "datafusion" not in sys.modules
        """,
        engine,
    )


def test_what_needs_datafusion_says_so():
    run(
        """
        from sverify.engine import plan_json, run_plan, written_plan

        plan = written_plan(plan_json(con, orders.filter(orders.amount > 10)))
        for attempt in (
            lambda: run_plan(con, plan, "datafusion"),
            lambda: plan_json(con, "SELECT * FROM orders"),
        ):
            try:
                attempt()
            except ImportError as e:
                assert "sverify[datafusion]" in str(e), e
            else:
                raise AssertionError("expected an ImportError")
        """
    )

"""A LIMIT without an ORDER BY (#928, D24): the reference allows any of the
input's rows, so `verify` proves the contract for every choice and `run`
takes the engine's; `refresh` commits one choice for good and refuses the
plan unless its order is total (`Rel.bags_fetch_two`)."""

import ibis
import pytest
from deltalake import DeltaTable
from ibis import _

import sverify as sv
from _pipelines import make_orders
from sverify.errors import RouteError
from sverify.io import DeltaSink


@sv.transform(requires={"orders": [_.amount >= 0, _.amount < 1_000]}, ensures=[_.amount >= 0])
def any_two(orders):
    """Two orders, whichever the engine reads first."""
    return orders.limit(2)


@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1_000, _.id.notnull(), sv.unique("id")]},
    ensures=[_.amount >= 0],
)
def first_two(orders):
    """The two orders with the smallest ids."""
    return orders.order_by("id").limit(2)


ROWS = [(1, "ada", 5), (2, "bob", 7), (3, "cy", 9)]


def test_verify_proves_every_choice_and_run_takes_one() -> None:
    con = sv.connect()
    con.create("t", ibis.schema({"id": "int64", "amount": "int64"}), [(1, 5), (2, 7), (3, 9)])
    t = con.table("t")
    report = sv.verify(t.limit(2), requires={"t": [_.amount >= 0]}, ensures=[_.amount >= 0])
    assert report.proved and not report.deterministic
    assert [p.op for p in report._tie_places] == ["fetch"]
    out = report.run(con, "duckdb")
    assert out.num_rows == 2


def test_refresh_refuses_and_says_to_order_the_rows(tmp_path) -> None:
    orders = make_orders(tmp_path / "orders", ROWS)
    node = any_two(orders).write(DeltaSink(str(tmp_path / "out")))
    with pytest.raises(RouteError, match="order the rows before the LIMIT") as err:
        node.refresh(engine="duckdb")
    assert "the fetch at relation" in str(err.value)
    assert "first(), last()" not in str(err.value)
    with pytest.raises(Exception):  # noqa: B017 - nothing was written
        DeltaTable(str(tmp_path / "out"))


def test_a_sinks_reproducible_does_not_open_the_rows(tmp_path) -> None:
    """No requirement on a rerun holds for a choice of rows: a coarse one is
    refused as well."""
    orders = make_orders(tmp_path / "orders", ROWS)
    coarse = sv.equivalent(rows="multiset", floats=sv.within(abs=1e9))
    node = any_two(orders).write(DeltaSink(str(tmp_path / "out"), reproducible=coarse))
    with pytest.raises(RouteError, match="not determined up to row order"):
        node.refresh(engine="duckdb")


def test_refresh_takes_a_limit_over_a_total_order(tmp_path) -> None:
    orders = make_orders(tmp_path / "orders", ROWS)
    node = first_two(orders).write(DeltaSink(str(tmp_path / "out")))
    node.refresh(engine="duckdb")
    ids = sorted(DeltaTable(str(tmp_path / "out")).to_pyarrow_table().column("id").to_pylist())
    assert ids == [1, 2]

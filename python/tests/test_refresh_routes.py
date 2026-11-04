"""Routes and determinism in `Node.refresh` (#444, D10 and D13): a refresh
with `route` takes each node's proof to the engine by a route, or refuses
before anything runs; a stored node whose result is not determined up to
row order is refused, since its sink commits each epoch once."""

import pytest
from deltalake import DeltaTable
from ibis import _

import sverify as sv
from _pipelines import doubled, make_orders, paid
from sverify.errors import RouteError
from sverify.io import DeltaSink


@sv.transform(requires={"orders": [_.amount >= 0, _.amount < 1_000]})
def any_amount(orders):
    """One amount per customer, whichever row `first` picks."""
    return orders.group_by("customer").aggregate(amount=orders.amount.first())


def test_refresh_reports_the_route(tmp_path) -> None:
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    node = doubled(paid(orders))
    for engine in ("duckdb", "polars"):
        out = node.refresh(engine=engine, route="auto")
        r = out["doubled"].route
        assert r is not None and r.kind == "reference" and r.engine == engine
        assert f"route on {engine}: reference" in str(out)
    plain = doubled(paid(orders)).refresh(engine="polars")
    assert plain["doubled"].route is None


def test_a_refused_route_refreshes_nothing(tmp_path) -> None:
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    node = doubled(paid(orders)).write(DeltaSink(str(tmp_path / "out")))
    with pytest.raises(
        RouteError, match="refused on duckdb: out: not verified under Profile.duckdb"
    ):
        node.refresh(route="native")
    with pytest.raises(Exception):  # noqa: B017 - nothing was written
        DeltaTable(str(tmp_path / "out"))
    node.refresh(route="reference")
    assert DeltaTable(str(tmp_path / "out")).to_pyarrow_table().num_rows == 1


def test_a_stored_node_needs_a_determined_result(tmp_path) -> None:
    """D10: an idempotent sink's epoch must give the same rows on a rerun."""
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "ada", 7)])
    open_pick = any_amount(orders)
    report = any_amount.last_report
    assert report is not None and not report.deterministic
    # Reported, not refused, where nothing is stored.
    route = open_pick.refresh(route="auto")["any_amount"].route
    assert route is not None and not route.deterministic and route.warnings
    stored = any_amount(orders).write(DeltaSink(str(tmp_path / "picked")))
    for how in (None, "auto"):
        with pytest.raises(RouteError, match="rerun must give the same"):
            stored.refresh(route=how)

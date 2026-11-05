"""A `SortRel` key may leave its direction unspecified or be clustered (#444
step 1c, D6 and D8 of `docs/core-semantics.md`): the checker reads the first
as ascending with NULLs last, the reference's choice, and the second as any
order with equal keys adjacent, which a sort gives."""

import json

import ibis
import pytest

from _sql_lift import TABLES
from sverify.engine import connect, run_checker, run_plan, written_plan
from sverify.sql_lift import lift

ORDERS = TABLES["orders"].select(["id", "price"])
SCHEMAS = {"orders": ibis.Schema.from_pyarrow(ORDERS.schema)}


def sort_plan(direction: str | None) -> dict:
    plan = lift("SELECT id, price FROM orders ORDER BY price", SCHEMAS).plan
    node = plan["relations"][0]["root"]["input"]
    while "sort" not in node:
        node = next(v for v in node.values() if isinstance(v, dict) and "input" in v)["input"]
    for key in node["sort"]["sorts"]:
        if direction is None:
            del key["direction"]
        else:
            key["direction"] = direction
    return plan


def directions(plan: dict) -> list[str | None]:
    found: list[str | None] = []

    def walk(x):
        if isinstance(x, dict):
            if "sort" in x and isinstance(x["sort"], dict) and "sorts" in x["sort"]:
                found.extend(k.get("direction") for k in x["sort"]["sorts"])
            for v in x.values():
                walk(v)
        elif isinstance(x, list):
            for v in x:
                walk(v)

    walk(plan)
    return found


@pytest.mark.parametrize(
    ("direction", "written"),
    [
        (None, "SORT_DIRECTION_UNSPECIFIED"),
        ("SORT_DIRECTION_UNSPECIFIED", "SORT_DIRECTION_UNSPECIFIED"),
        ("SORT_DIRECTION_CLUSTERED", "SORT_DIRECTION_CLUSTERED"),
    ],
)
def test_checked_and_written_back(direction, written):
    plan = json.dumps(sort_plan(direction))
    code, out, err = run_checker((), plan)
    assert code == 0, err or out
    assert directions(json.loads(written_plan(plan))) == [written]


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_unspecified_puts_nulls_last(engine):
    con = connect("duckdb")
    con.create("orders", ORDERS.schema, [tuple(r.values()) for r in ORDERS.to_pylist()])
    plan = written_plan(json.dumps(sort_plan("SORT_DIRECTION_UNSPECIFIED")))
    prices = run_plan(con, plan, engine).column("price").to_pylist()
    assert prices == [-1.5, 0.0, 2.5, 10.0, None]


def test_windows_state_a_direction():
    plan = lift("SELECT id, ROW_NUMBER() OVER (ORDER BY price) AS n FROM orders", SCHEMAS).plan
    text = json.dumps(plan).replace("SORT_DIRECTION_ASC_NULLS_LAST", "SORT_DIRECTION_CLUSTERED")
    code, out, err = run_checker((), text)
    assert code != 0
    assert "clustered" in (err or out)

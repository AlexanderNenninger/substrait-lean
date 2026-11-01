"""Tests of the tour's transforms (`notebooks/`), written with sverify's pytest
plugin: the tests a data engineer would keep next to these jobs.

Each notebook runs once (`App.run`), and its transforms and schemas are
taken from what its cells define, so the tests follow the notebooks. The
nodes are rebuilt over in-memory sources (`sv_source`) with the notebooks'
schemas.
"""

import datetime as dt
import functools
import importlib.util
import warnings
from pathlib import Path
from typing import Any

import pytest
from hypothesis import given, settings

from sverify.testing import assert_contract, assert_engines_agree, cases

NOTEBOOKS = Path(__file__).resolve().parents[2] / "notebooks"

#: `python/tests` copied out (the wheel's tests): there the notebooks are not here.
pytestmark = pytest.mark.skipif(not NOTEBOOKS.is_dir(), reason="the notebooks are not here")


@functools.cache
def notebook(name: str) -> dict[str, Any]:
    """The names a notebook's cells define, after running it."""
    pytest.importorskip("marimo")
    spec = importlib.util.spec_from_file_location(name, NOTEBOOKS / f"{name}.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        _, defs = module.app.run()
    return dict(defs)


def minute(m: int, s: int = 0) -> dt.datetime:
    return dt.datetime(2026, 7, 1, 12, m, s)


# -- 0. Start here ---------------------------------------------------------------


def test_doubled(sv_source, sv_engine):
    nb = notebook("00_start_here")
    orders = sv_source([], {"id": "int64", "customer": "string", "amount": "int64"}, name="orders")
    data = {"orders": [(1, "ada", 30), (2, "bob", 5), (3, None, 11)]}
    expected = [(1, 60), (3, 22)]
    assert_contract(nb["doubled"](orders), data=data, expected=expected, engine=sv_engine)


# -- 1. Duplicate card payments --------------------------------------------------


def payments(sv_source):
    nb = notebook("01_duplicate_payments")
    transactions = sv_source([], nb["TXN_SCHEMA"], name="transactions")
    return nb, transactions.pipe(nb["duplicate_payments"])


def test_a_double_charge_is_found_once(sv_source):
    _, node = payments(sv_source)
    data = {
        "transactions": [
            (1, 7, "cafe", 450, minute(0)),
            (2, 7, "cafe", 450, minute(2)),  # the double charge
            (3, 7, "cafe", 450, minute(8)),  # six minutes after 2: a second coffee
            (4, 8, "cafe", 450, minute(1)),  # another card
            (5, 7, "bakery", 450, minute(1)),  # another merchant
        ]
    }
    expected = [(1, 2, 7, "cafe", 450, minute(0), minute(2))]
    assert_contract(node, data=data, expected=expected)
    assert_engines_agree(node, data)


def test_refunds(sv_source):
    nb, node = payments(sv_source)
    dups = sv_source([], node.schema.to_pyarrow(), name="dups")
    data = {"dups": [(1, 2, 7, "cafe", 450, minute(0), minute(2))]}
    assert_contract(dups.pipe(nb["refunds"]), data=data, expected=[(2, "cafe", 450)])


def test_duplicates_are_within_five_minutes(sv_source):
    _, node = payments(sv_source)

    @settings(max_examples=20, deadline=None, database=None)
    @given(cases(node, max_rows=4))
    def check(data):
        out = assert_contract(node, data=data)
        by_id = {t["txn_id"]: t for t in data["transactions"].to_pylist()}
        for row in out.to_pylist():
            first, dup = by_id[row["first_txn"]], by_id[row["duplicate_txn"]]
            assert (first["card_id"], first["merchant"]) == (dup["card_id"], dup["merchant"])
            assert dt.timedelta(0) <= dup["ts"] - first["ts"] <= dt.timedelta(minutes=5)

    check()


# -- 2. Sensor alerts ------------------------------------------------------------


def test_alerts_on_the_first_batch(sv_source, sv_engine):
    nb = notebook("02_sensor_alerts")
    readings = sv_source([], nb["READING"], name="readings")
    node = readings.pipe(nb["alerts"])
    data = {"readings": nb["first"]}
    # Device 2's missing reading breaks its run; device 3's NaN is not hot.
    assert_contract(node, data=data, expected=[(1, minute(3), 33.0)], engine=sv_engine)


def test_alerts_are_input_readings(sv_source):
    nb = notebook("02_sensor_alerts")
    node = nb["alerts"](sv_source([], nb["READING"], name="readings"))

    @settings(max_examples=20, deadline=None, database=None)
    @given(cases(node, max_rows=5))
    def check(data):
        out = assert_engines_agree(node, data)
        readings = {(r["device_id"], r["ts"]): r for r in data["readings"].to_pylist()}
        for row in out.to_pylist():
            assert readings[row["device_id"], row["ts"]] == row

    check()


# -- 3. An orders mart -----------------------------------------------------------


def test_daily_city_revenue(sv_source):
    nb = notebook("03_orders_mart")
    orders = sv_source([], nb["ORDERS"], name="orders")
    history = sv_source([], nb["HISTORY"], name="history")
    node = orders.pipe(nb["daily_city_revenue"], history=history)
    may = nb["may"]
    data = {"orders": nb["orders_v0"], "history": nb["history_v0"]}
    # Customer 1 moved from Paris to Lyon on May 2.
    expected = [
        ("Paris", may(1, 0), 1, 1200),
        ("Lyon", may(3, 0), 1, 800),
        ("Rome", may(3, 0), 2, 4699),
        ("Oslo", may(4, 0), 1, 999),
    ]
    assert_contract(node, data=data, expected=expected)
    assert_engines_agree(node, data)
    # An order before the customer's first known city counts as "unknown".
    data["orders"] = [(9, 1, may(1, 0) - dt.timedelta(days=1), 10)]
    assert_contract(
        node, data=data, expected=[("unknown", may(1, 0) - dt.timedelta(days=1), 1, 10)]
    )

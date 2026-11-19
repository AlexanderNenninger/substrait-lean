"""A threshold computed from the data (#1608 item 12).

`qty > (SELECT AVG(qty) FROM orders)` compares with a mean rounded to a double,
whose last bit differs between engines, so the route refuses it
(`routes._THRESHOLD`). The exact columns, `qty * COUNT(qty) > SUM(qty)`, are
another query (the exact mean, not the rounded one); every engine runs it and
agrees. Its product fits `BIGINT` once the column has a bound and the table a
row cap (12e of #1608: a `COUNT` is at most the cap); without the cap it can
overflow, and the checker says so."""

import pyarrow as pa
import pytest

import sverify as sv
from _engines import PROFILED

ORDERS = {"orders": pa.schema([("id", pa.int64()), ("qty", pa.int64())])}
MEAN = "SELECT id FROM orders WHERE qty > (SELECT AVG(qty) FROM orders)"
EXACT = (
    "SELECT id FROM orders "
    "WHERE qty * (SELECT COUNT(qty) FROM orders) > (SELECT SUM(qty) FROM orders)"
)


def test_the_mean_is_refused_and_the_message_names_the_exact_columns():
    report = sv.verify(MEAN, tables=ORDERS, on_inferred="warn")
    with pytest.raises(sv.errors.RouteError, match=r"COUNT\(y\) > SUM\(y\)"):
        report.to_sql("duckdb")


#: The exit's needs: a bound on the column and a row cap on the table.
BOUNDED = {"orders": ["qty IS NULL OR qty BETWEEN -1000000 AND 1000000", sv.max_rows(10**9)]}


@pytest.mark.parametrize("engine", PROFILED)
def test_the_exact_columns_are_proved_and_run_on_every_engine(engine):
    report = sv.verify(EXACT, tables=ORDERS, requires=BOUNDED, on_inferred="warn")
    assert report.errors == []
    assert report.verdict == "proved"
    con = sv.connect()
    con.put("orders", pa.table({"id": [1, 2, 3, 4, 5], "qty": [1, 2, 3, 10, None]}))
    got = report.run(con, engine)
    # The mean of 1, 2, 3 and 10 is 4: only 10 is above it. NULL is never above.
    assert sorted(r["id"] for r in got.to_pylist()) == [4]
    empty = sv.connect()
    empty.put("orders", pa.table({"id": pa.array([], pa.int64()), "qty": pa.array([], pa.int64())}))
    assert report.run(empty, engine).num_rows == 0


def test_without_a_row_cap_the_product_may_overflow():
    unbounded = {"orders": ["qty IS NULL OR qty BETWEEN -1000000 AND 1000000"]}
    report = sv.verify(EXACT, tables=ORDERS, requires=unbounded, on_inferred="warn")
    assert [i.kind for i in report.errors] == ["overflow"]


def test_a_bounded_mean_of_integers_is_exact_and_the_threshold_runs():
    # 12b-1 (#1608): with `N · max M 1 <= 2^52` every engine's mean of the
    # converted integers is the reference's (`AvgOrder.int_exact`), so the
    # mean's column has no tolerance and the threshold keeps the same rows.
    report = sv.verify(MEAN, tables=ORDERS, requires=BOUNDED, on_inferred="warn")
    report.to_sql("duckdb")
    mean = sv.verify(
        "SELECT AVG(qty) AS m FROM orders", tables=ORDERS, requires=BOUNDED, on_inferred="warn"
    )
    assert mean._epsilon is not None
    bound = mean._epsilon["m"]["bounds"]["abs"]
    assert bound == {"proved": True, "value": 0}


def test_too_many_rows_keep_the_mean_refused():
    many = {"orders": [BOUNDED["orders"][0], sv.max_rows(2**33)]}
    report = sv.verify(MEAN, tables=ORDERS, requires=many, on_inferred="warn")
    with pytest.raises(sv.errors.RouteError, match=r"COUNT\(y\) > SUM\(y\)"):
        report.to_sql("duckdb")

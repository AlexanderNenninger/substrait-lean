"""A threshold computed from the data (#1608 item 12).

`qty > (SELECT AVG(qty) FROM orders)` compares with a mean rounded to a double,
whose last bit differs between engines, so the route refuses it
(`routes._THRESHOLD`). The exact columns, `qty * COUNT(qty) > SUM(qty)`, are
another query (the exact mean, not the rounded one); every engine runs it and
agrees. The product can overflow `BIGINT` for any row count, so the checker
leaves that as an error and the run states it."""

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


@pytest.mark.parametrize("engine", PROFILED)
def test_the_exact_columns_run_on_every_engine(engine):
    report = sv.verify(EXACT, tables=ORDERS, on_inferred="warn")
    # 12e (#1608): a COUNT does not read the row cap yet, so the product `qty *
    # COUNT(qty)` stays an `overflow` error and the run says `unverified=True`.
    # When a COUNT reads `sv.max_rows`, this test states `between` and `max_rows`,
    # asserts a proved verdict and drops `unverified=True`: that failing is 12e's
    # tripwire.
    assert [i.kind for i in report.errors] == ["overflow"]
    con = sv.connect()
    con.put("orders", pa.table({"id": [1, 2, 3, 4, 5], "qty": [1, 2, 3, 10, None]}))
    got = report.run(con, engine, unverified=True)
    # The mean of 1, 2, 3 and 10 is 4: only 10 is above it. NULL is never above.
    assert sorted(r["id"] for r in got.to_pylist()) == [4]
    empty = sv.connect()
    empty.put("orders", pa.table({"id": pa.array([], pa.int64()), "qty": pa.array([], pa.int64())}))
    assert report.run(empty, engine, unverified=True).num_rows == 0

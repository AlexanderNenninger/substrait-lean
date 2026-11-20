"""`finite="aggregates"` (the lens of `semantics="duckdb"`, #2057): on Polars an
operation's overflow to ±∞ returns the infinity, as DuckDB and Spark do, and an
aggregate's still raises."""

import ibis
import pytest

from sverify.engine import connect, run_plan, written_plan
from sverify.ibis_substrait import to_substrait_json

pytestmark = pytest.mark.backend("polars")

T = ibis.table({"a": "float64", "b": "float64"}, name="t")


def run(expr, finite):
    con = connect("polars")
    con.create("t", ibis.schema({"a": "float64", "b": "float64"}), [(1e308, 10.0), (1e308, 10.0)])
    return run_plan(con, written_plan(to_substrait_json(expr)), "polars", finite=finite)


def test_an_operation_overflows_to_infinity_under_the_lens() -> None:
    out = run(T.select(p=T.a * T.b), "aggregates").to_pylist()
    assert [r["p"] for r in out] == [float("inf")] * 2


def test_an_operation_overflow_raises_when_every_overflow_is_checked() -> None:
    with pytest.raises(Exception, match="overflow"):
        run(T.select(p=T.a * T.b), True)


@pytest.mark.parametrize("finite", [True, "aggregates"])
def test_a_sum_overflow_raises_unless_no_overflow_is_checked(finite) -> None:
    with pytest.raises(Exception, match="overflow"):
        run(T.aggregate(s=T.a.sum()), finite)
    assert run(T.aggregate(s=T.a.sum()), False).to_pylist() == [{"s": float("inf")}]

"""`log(x, b)` with a NULL argument is NULL on Polars before the domain is read (#1990):
`Expr.issues` reads a call with both arguments present, and under Kleene `OR` a NULL
operand beside a true domain test would still raise."""

import ibis
import pytest

from sverify.engine import connect, run_plan, written_plan
from sverify.ibis_substrait import to_substrait_json

pytestmark = pytest.mark.backend("polars")

T = ibis.table({"k": "int64", "x": "float64", "b": "float64"}, name="t")


@pytest.mark.parametrize(
    ("x", "b", "raises"),
    [
        (None, 0.0, False), (None, 1.0, False), (None, -1.0, False),  # NULL before the domain
        (-1.0, None, False), (0.0, None, False),
        (1.0, 0.0, True), (5.0, 1.0, True), (-1.0, 2.0, True),
    ],
)  # fmt: skip
def test_log_of_a_null_argument_is_null_before_the_domain_is_read(
    x: float | None, b: float | None, raises: bool
) -> None:
    con = connect("polars")
    con.create("t", ibis.schema({"k": "int64", "x": "float64", "b": "float64"}), [(0, x, b)])
    plan = written_plan(to_substrait_json(T.select(T.k, v=T.x.log(T.b))))
    if raises:
        with pytest.raises(Exception, match="domain"):
            run_plan(con, plan, "polars")
    else:
        assert run_plan(con, plan, "polars").to_pylist() == [{"k": 0, "v": None}]

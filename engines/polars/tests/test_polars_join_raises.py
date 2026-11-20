"""A join whose condition raises on a pair that passes its other comparisons raises on
Polars, for every join type (#1857): `Rel.Raises` holds on the pair, and DuckDB raises.

A left join reads its matches once: read twice (an anti join, then a union), Polars
caches them and fuses the filter into a nested-loop join below the `guard`, which then
never sees a pair the comparison rejects."""

import json

import ibis
import pytest

from sverify.engine import connect, run_plan, written_plan
from sverify.ibis_substrait import to_substrait_json
from sverify.testing import inline_tables, lean_values

pytestmark = pytest.mark.backend("polars")

T = ibis.table({"a": "float64", "i": "int64", "k": "int64"}, name="t")
U = ibis.table({"b": "float64", "j": "int64", "k": "int64"}, name="u")
#: `i // (i - j)` divides by zero on the pair (1, 1), which also has a > b.
RAISES = (T.a > U.b) & ((T.i // (T.i - U.j)) > 0)


def run(how: str, cond, t_rows: list[tuple], u_rows: list[tuple]) -> list[dict]:
    con = connect("polars")
    con.create("t", ibis.schema({"a": "float64", "i": "int64", "k": "int64"}), t_rows)
    con.create("u", ibis.schema({"b": "float64", "j": "int64", "k": "int64"}), u_rows)
    plan = written_plan(to_substrait_json(T.join(U, cond, how=how)))
    return run_plan(con, plan, "polars").to_pylist()


@pytest.mark.parametrize("how", ["inner", "left", "semi", "anti"])
@pytest.mark.parametrize("keyed", [False, True], ids=["keyless", "keyed"])
def test_a_pair_that_passes_the_comparison_and_raises_raises(how: str, keyed: bool) -> None:
    cond = RAISES & (T.k == U.k) if keyed else RAISES
    with pytest.raises(Exception, match="divide by zero"):
        run(how, cond, [(5.0, 1, 0)], [(2.0, 1, 0)])


def test_a_left_join_keeps_the_references_rows_and_order() -> None:
    """Matched and unmatched rows, a left row with several matches, and NULL keys: the rows
    and their order are `Rel.eval`'s."""
    t_rows = [(1.0, 2, 0), (5.0, 3, 1), (None, 4, 1), (9.0, 5, 2), (0.5, 6, 3)]
    u_rows = [(2.0, 1, 1), (3.0, 2, 1), (4.0, 3, 9), (None, 4, 1), (1.0, 9, 2)]
    cond = (T.k == U.k) & (T.a > U.b)
    con = connect("polars")
    con.create("t", ibis.schema({"a": "float64", "i": "int64", "k": "int64"}), t_rows)
    con.create("u", ibis.schema({"b": "float64", "j": "int64", "k": "int64"}), u_rows)
    plan = written_plan(to_substrait_json(T.join(U, cond, how="left")))
    inlined = json.dumps(inline_tables(json.loads(plan), {"t": t_rows, "u": u_rows}))
    got = [tuple(r.values()) for r in run_plan(con, plan, "polars").to_pylist()]
    assert got == lean_values(inlined)

"""A plan the checker writes declares exactly the functions it calls (#1787
item 5, ruling 223): every anchor it references is declared, none other is,
and each engine runs the smaller plan."""

import json

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify.engine import connect, put_table, run_plan, written_plan

T = ibis.table({"a": "int64", "b": "float64", "s": "string"}, name="t")
PLANS = {
    "no function": T.select("a"),
    "arithmetic": T.select(x=T.a * 2 + 1, y=T.b / 2.0),
    "filter and aggregate": T.filter(T.a > 0).group_by("s").agg(n=T.a.count(), m=T.b.max()),
    "strings": T.select(p=T.s.startswith("x"), n=T.s.length()),
    "window": T.mutate(r=ibis.row_number().over(group_by="s", order_by="a")),
    "double sum": T.group_by("s").agg(t=T.b.sum()),
    # DISTINCT on a key: the checker rewrites it away (`run_plan`; under the
    # exact lens, since the table has a double).
    "distinct on a key": T.select("a", x=T.a + 1).distinct(),
}
# Bounded, but a double SUM may still overflow to ±∞: an assumed issue.
REQUIRES = {"t": [_.a.between(-10, 10), _.b.between(-1e300, 1e300), sv.unique("a")]}
ROWS = pa.table({"a": [3, -1, 2], "b": [1.5, 2.0, -0.5], "s": ["x", "y", "x"]})


def _refs(node) -> set[int]:
    if isinstance(node, dict):
        own = {node["functionReference"]} if "functionReference" in node else set()
        return own.union(*(_refs(v) for v in node.values()))
    if isinstance(node, list):
        return set().union(*(_refs(v) for v in node))
    return set()


def _declared(plan: dict) -> set[int]:
    return {
        e["extensionFunction"]["functionAnchor"]
        for e in plan.get("extensions", [])
        if "extensionFunction" in e
    }


def _verify(name: str):
    # A SUM of doubles has no bound without a row cap, and a quotient of doubles differs on
    # Polars by its reciprocal (#2486, #2573), so the exact lens is not met; this test is about
    # the plan's functions, not the doubles' lens.
    plan_lens = name in ("double sum", "arithmetic")
    lens = sv.equivalent(floats="plan") if plan_lens else sv.equivalent()
    return sv.verify(PLANS[name], requires=REQUIRES, ensures=[lens])


def _plans(report) -> dict[str, str]:
    assert report.internal_plan is not None
    out = {"written": written_plan(report.internal_plan)}
    for kind, plan in (("optimized", report._optimized), ("run_plan", report._run_plan)):
        if plan is not None:
            out[kind] = json.dumps(plan)
    if report._assumed_check is not None:
        out["assumed_check"] = json.dumps(report._assumed_check[0])
    return out


@pytest.mark.parametrize("name", PLANS)
def test_a_written_plan_declares_exactly_the_functions_it_calls(name):
    report = _verify(name)
    for kind, text in _plans(report).items():
        plan = json.loads(text)
        refs = _refs(plan["relations"])
        assert _declared(plan) == refs, kind


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
@pytest.mark.parametrize("name", PLANS)
def test_each_engine_runs_the_smaller_plan(engine, name):
    pytest.importorskip(engine)
    report = _verify(name)
    con = connect()
    put_table(con, "t", ROWS)
    for kind, plan in _plans(report).items():
        if kind != "assumed_check":
            assert run_plan(con, plan, engine).num_rows == report.run(con, engine).num_rows, kind

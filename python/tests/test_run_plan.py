"""The plan an engine runs (#1787, item 2): the checker's rewrite where every
gate passes (`Request.runPlanIn`, `SubstraitLean/RunPlan.lean`), the plan as
written otherwise, with the gate that kept it named (`Report._run_gate`).

Each fallback path has a test that asserts on its own gate. The rules are off
by default (`Rule.onByDefault`); these tests turn them on through
`sverify.contracts._RULES`, as the bench does.
"""

import json
import re
import subprocess

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from _repo import ROOT, needs_repo
from sverify import contracts, routes
from sverify._checker import _checker_file
from sverify.errors import UnsupportedError
from sverify.sql import to_sql
from sverify_duckdb.dialect import DUCKDB

T = ibis.table({"id": "int64", "g": "int64", "a": "int64"}, name="t")
KEY = {"t": [sv.unique("id"), _.a >= 0, _.a <= 1000]}
DATA = pa.table({"id": [1, 2, 3, 4], "g": [1, 1, 2, 2], "a": [5, 6, 7, 8]})
DISTINCT = "DISTINCT on a key"


@pytest.fixture
def rules(monkeypatch):
    """Turn the named rules on for the checker's plan to run."""

    def on(*names: str) -> None:
        monkeypatch.setattr(contracts, "_RULES", list(names))

    return on


def con():
    c = sv.connect()
    c.put("t", DATA)
    return c


def sorted_rows(table: pa.Table) -> list:
    return sorted(table.to_pylist(), key=json.dumps)


def test_accepted_rewrite_runs_and_shrinks_the_sql(rules):
    rules(DISTINCT)
    report = sv.verify(T.distinct(), requires=KEY)
    assert report._run_gate is None and report._run_plan is not None
    assert "GROUP BY" not in to_sql(report._run_plan, DUCKDB)
    rules()
    as_written = sv.verify(T.distinct(), requires=KEY)
    c = con()
    for engine in ["duckdb", "polars"]:
        assert sorted_rows(report.run(c, engine)) == sorted_rows(as_written.run(c, engine))
        assert engine not in report._run_gates


def test_an_unchecked_run_runs_the_plan_as_written(rules):
    # Every rewrite rests on the preconditions: a run that does not check
    # them on its data runs what the user wrote (ruling 150, C1).
    rules(DISTINCT)
    report = sv.verify(T.distinct(), requires=KEY)
    assert report._run_plan is not None
    out = report.run(con(), "duckdb", check_requires=False)
    assert out.num_rows == DATA.num_rows
    assert report._run_gates["duckdb"] == "unchecked"
    assert report._run_gate is None


def test_to_sql_writes_the_plan_as_written(rules):
    # Nothing checks the data of whoever runs the SQL (ruling 150, C1).
    rules(DISTINCT)
    report = sv.verify(T.distinct(), requires=KEY)
    assert report._run_plan is not None
    assert "GROUP BY" in report.to_sql()
    assert report._run_gates["to_sql"] == "unchecked"
    # An explicit opt-in, for data known to meet the preconditions.
    assert "GROUP BY" not in report.to_sql(optimize=True)
    assert "to_sql" not in report._run_gates


def test_optimize_false_runs_the_plan_as_written(rules):
    rules(DISTINCT)
    report = sv.verify(T.distinct(), requires=KEY)
    assert report.run(con(), "duckdb", optimize=False).num_rows == DATA.num_rows
    assert report._run_gates["duckdb"] == "optimize"


def test_rule_off_keeps_the_plan_as_written(rules):
    rules()
    report = sv.verify(T.distinct(), requires=KEY)
    assert report._rewrites == [DISTINCT]
    assert report._run_plan is None and report._run_gate == "no_rewrite"


def test_another_profile_keeps_the_plan_as_written(rules):
    rules(DISTINCT)
    report = sv.verify(T.distinct(), requires=KEY, semantics="duckdb")
    assert report._run_gate == "profile"


def test_a_sequence_without_an_order_by_keeps_the_plan_as_written(rules):
    rules(DISTINCT)
    report = sv.verify(T.distinct(), requires=KEY, ensures=[sv.equivalent(rows="sequence")])
    assert report._run_gate == "rows"


def test_a_sequence_under_an_order_by_takes_the_rewrite(rules):
    rules(DISTINCT)
    report = sv.verify(
        T.distinct().order_by("id"), requires=KEY, ensures=[sv.equivalent(rows="sequence")]
    )
    assert report._run_gate is None and report._run_plan is not None
    assert report.run(con()).column("id").to_pylist() == [1, 2, 3, 4]


def test_an_issue_in_the_rewrite_keeps_the_plan_as_written(rules):
    # The SUM may overflow in both plans: an assumed issue the rewrite keeps,
    # and no rule has its lemma that it sees no more rows (`Rule.keepsIssues`).
    rules(DISTINCT)
    report = sv.verify(
        (d := T.distinct()).aggregate(s=d.a.sum()), requires={"t": [sv.unique("id")]}
    )
    assert DISTINCT in report._rewrites
    assert report._run_gate == "issues"


def test_doubles_within_a_bound_keep_the_plan_as_written(rules):
    rules(DISTINCT)
    d = ibis.table({"id": "int64", "x": "float64"}, name="d")
    report = sv.verify(d.distinct(), requires={"d": [sv.unique("id")]})
    assert DISTINCT in report._rewrites
    assert report._run_gate == "near"


def test_doubles_compared_exactly_take_the_rewrite(rules):
    rules(DISTINCT)
    d = ibis.table({"id": "int64", "x": "float64"}, name="d")
    report = sv.verify(
        d.distinct(), requires={"d": [sv.unique("id")]}, ensures=[sv.equivalent(floats="exact")]
    )
    assert report._run_gate is None


def test_a_function_the_plan_does_not_call_keeps_the_plan_as_written(rules):
    # GROUP BY through functional dependencies carries a dropped column by MIN,
    # which the plan as written does not call (ruling 129, question 4).
    rule = "GROUP BY columns that others determine"
    rules(rule)
    line = ibis.table({"k": "int64", "p": "int64"}, name="line")
    orders = ibis.table({"ok": "int64", "d": "int64"}, name="ord")
    expr = line.join(orders, line.k == orders.ok).group_by([line.k, orders.d]).agg(n=line.p.count())
    report = sv.verify(expr, requires={"ord": [sv.unique("ok")]})
    assert rule in report._rewrites
    assert report._run_gate in ("reads", "functions")


def test_a_writer_that_refuses_the_rewrite_runs_the_plan_as_written(rules):
    rules(DISTINCT)
    report = sv.verify(T.distinct(), requires=KEY)
    assert report._run_plan is not None
    rewrite = json.dumps(report._run_plan)

    def writer(plan: str) -> str:
        if plan == rewrite:
            raise UnsupportedError("this engine's writer refuses the rewrite")
        return plan

    rechecked = []
    plan = report._plan_to_run("translated", checked=True, engine="refusing")
    assert report._with_plan(plan, "refusing", writer, rechecked.append) != rewrite
    assert rechecked and rechecked[0] != rewrite
    assert report._run_gates == {"refusing": "writer"}
    # The gate is that engine's: the checker's stays, and another engine's run
    # takes the rewrite (ruling 150, C2).
    assert report._run_gate is None
    assert report._plan_to_run("translated", checked=True, engine="duckdb") == rewrite
    report.run(con(), "duckdb")
    assert "duckdb" not in report._run_gates


@pytest.mark.parametrize("kind", ["translated", "transfer", "native", "recheck", "unverified"])
def test_the_route_table_decides_which_plan_runs(rules, kind):
    rules(DISTINCT)
    report = sv.verify(T.distinct(), requires=KEY)
    rewrite = json.dumps(report._run_plan)
    taken = report._plan_to_run(kind, checked=True, engine=kind) == rewrite
    assert taken == routes.runs_rewrite(kind)
    assert report._run_gates.get(kind) == (None if taken else "route")
    assert routes.runs_rewrite(kind) == (kind in ("translated", "transfer"))


@needs_repo
def test_the_doc_states_the_checkers_gate():
    out = subprocess.run(
        [str(_checker_file()), "--rules"], capture_output=True, text=True, check=True
    ).stdout
    table = {r["name"]: r["on"] for r in json.loads(out)}
    doc = (ROOT / "docs" / "optimizations.md").read_text()
    section = doc[doc.index("### The gate") :]
    rows = dict(
        (name, on == "on")
        for name, on in re.findall(r"^\| ([^|`]+?) \| (on|off) \|", section, re.M)
    )
    assert rows == table

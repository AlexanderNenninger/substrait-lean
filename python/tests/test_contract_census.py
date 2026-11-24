"""The contract census (`catalogue/contracts.toml`) holds as recorded.

Each case, a contract on an aggregate of doubles or a control, is verified
and routed to every engine again exactly as
`python -m sverify_dev.contract_census --write` recorded it in
`catalogue/contracts.json`: proved, tested (with its causes) or refused (with
the reason). A change to the checker, the routes or the engines' tables that
moves a contract from one outcome to another shows up here; regenerate with
`--write` and review the diff.
"""

import json

import pytest

from sverify_dev import contract_census as cc

if not cc.CASES.is_file():
    # An installed wheel (as the Wheels workflow tests it) has no repository.
    pytest.skip("the census lives in the repository, not in the wheel", allow_module_level=True)

CASES = cc.load_cases()
RESULTS = json.loads(cc.RESULTS.read_text())


def test_well_formed():
    ids = [c.id for c in CASES]
    assert len(ids) == len(set(ids))
    assert 30 <= len(ids) <= 60
    assert sorted(RESULTS) == sorted(ids)
    # Every outcome falls into one of the table's classes.
    known = {"proved"} | {name for _, name in cc.TESTED + cc.REFUSED}
    found = {cc.cause_of(r) for res in RESULTS.values() for r in res["engines"].values()}
    assert found <= known
    assert "| total refused" in cc.table(RESULTS)


def test_every_outcome_names_an_exit():
    """#1205: every refusal and every tested route names the issue or the
    option that lifts it."""
    assert cc.unnamed(RESULTS) == []


@pytest.mark.parametrize("case", CASES, ids=lambda c: c.id)
def test_outcome_holds(case):
    got = cc.census_case(case, cc.cat.load_schemas())
    assert got == RESULTS[case.id]


#: The double output columns the checker's `ε` leaves out because every engine computes them
#: exactly: a maximum, a minimum, a median, or an input column passed through.
EXACT_DOUBLES = {
    "median-range": {"med"},
    "avg-le-max": {"mx"},
    "min-le-avg": {"mn"},
    "sum-ge-max": {"top"},
    "running-sum": {"value"},
    "moving-avg": {"value"},
    "above-group-avg": {"value"},
    "zscore-outliers": {"value"},
    "control-max-double": {"mx"},
    "control-max-having": {"mx"},
    "control-max-exact": {"mx"},
}

#: Plans whose `ε` is empty though a `SUM` or `AVG` is among their outputs (a top-n or a rank
#: over it): a known gap (#2486), listed so that no other plan joins it unseen. A rule that
#: refuses every plan with an empty `ε` and a row that bounds doubles per plan moves dozens
#: of route pins (a projection of `exp`, TPC-DS q07), so it is not made here.
NO_EPSILON = {"top-n-sum", "top-1-avg", "rank-by-sum"}


@pytest.mark.parametrize("case", CASES, ids=lambda c: c.id)
def test_epsilon_names_every_inexact_double_output(case):
    """#2486: the realization meets a row that bounds doubles per plan against the plan's `ε`,
    so a double output the checker's `ε` leaves out must be computed exactly. A plan that
    loses a column's `ε` fails here, unless it is listed as one that has none."""
    report = cc.report_of(case, cc.cat.load_schemas())
    doubles = {c for c, t in report.output.items() if t.is_floating()}
    missing = doubles - set(report._epsilon or {}) - EXACT_DOUBLES.get(case.id, set())
    assert bool(missing) == (case.id in NO_EPSILON), (missing, report._epsilon)

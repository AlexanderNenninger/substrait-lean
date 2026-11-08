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


@pytest.mark.parametrize("case", CASES, ids=lambda c: c.id)
def test_outcome_holds(case):
    got = cc.census_case(case, cc.cat.load_schemas())
    assert got == RESULTS[case.id]

"""The `sverify check` action's SARIF merge (`actions/check/merge_sarif.py`, #770)."""

import importlib.util

import pytest

from _repo import ROOT, needs_repo

pytestmark = needs_repo


@pytest.fixture(scope="module")
def merge():
    path = ROOT / "actions" / "check" / "merge_sarif.py"
    spec = importlib.util.spec_from_file_location("merge_sarif", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.merge


def log(rules, results):
    return {
        "version": "2.1.0",
        "runs": [
            {
                "tool": {"driver": {"name": "sverify", "rules": [{"id": r} for r in rules]}},
                "results": [{"ruleId": r} for r in results],
            }
        ],
    }


def test_the_runs_merge_into_one_with_the_union_of_rules(merge):
    out = merge([log(["a", "b"], ["a"]), log(["b", "c"], ["b", "c"])])
    (run,) = out["runs"]
    assert [r["id"] for r in run["tool"]["driver"]["rules"]] == ["a", "b", "c"]
    assert [r["ruleId"] for r in run["results"]] == ["a", "b", "c"]


def test_one_log_stays_as_it_is(merge):
    one = log(["a"], ["a"])
    assert merge([one]) == log(["a"], ["a"])

"""sverify's own proposers (`sverify.proposers`, #2247): one interface for
the inference's bounds and the counterexample search."""

from __future__ import annotations

import ibis

from sverify import counterexample, proposers
from sverify.counterexample import Counterexample
from sverify.proposers import INFER, SEARCH, Obligation, Verdict

ORDERS = {"orders": ibis.schema({"id": "!int64", "amount": "int64"})}


def test_the_built_in_proposers_are_listed():
    found = proposers.proposers()
    assert found["infer"] is INFER and found["search"] is SEARCH
    assert INFER.kinds == ("precondition",) and SEARCH.kinds == ("counterexample",)


def test_infer_proposes_conditions_unconfirmed():
    needs = [
        {"table": "orders", "col": 1, "lo": "0", "hi": None},
        {"table": "orders", "col": 1, "not_null": True},
        {"table": "missing", "col": 0, "lo": "0", "hi": None},
    ]
    p = INFER.propose(Obligation("precondition", ORDERS, {"needs": needs}))
    assert p is not None and p.proposer == "infer" and p.verdict is None
    assert list(p.value) == ["orders"]
    assert [c.column for c in p.value["orders"]] == ["amount", "amount"]


def test_infer_has_nothing_for_no_bounds():
    assert INFER.propose(Obligation("precondition", ORDERS, {"needs": []})) is None


def test_search_proposals_come_confirmed(monkeypatch):
    seen = {}
    hit = Counterexample({"orders": [(1, -1)]}, [(-1,)], {"orders": ["id", "amount"], "": ["x"]})

    def search(schemas, **kw):
        seen.update(kw, schemas=schemas)
        return hit

    monkeypatch.setattr(counterexample, "search", search)
    p = SEARCH.propose(Obligation("counterexample", ORDERS, {"ensures": {}, "budget": 3}))
    assert p is not None and p.value is hit and p.verdict == Verdict(True, "Rel.eval")
    assert seen == {"ensures": {}, "budget": 3, "schemas": ORDERS}
    monkeypatch.setattr(counterexample, "search", lambda schemas, **kw: None)
    assert SEARCH.propose(Obligation("counterexample", ORDERS, {})) is None

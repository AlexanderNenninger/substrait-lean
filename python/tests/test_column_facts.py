"""`Report.facts` as data (#704, ruling 184): `ColumnFacts` agrees with
`Report.output`, rests on the stated preconditions alone under
`on_inferred="error"`, and each of its fields is a postcondition that proves."""

from __future__ import annotations

import math

import ibis
import pytest
from ibis import _

import sverify as sv
from _repo import needs_repo
from sverify.report import ColumnFacts

S = {"s": {"mrr": "BIGINT", "n": "BIGINT"}}


def test_facts_are_data_and_words():
    r = sv.verify("select k, count(*) as c from t group by k", tables={"t": {"k": "VARCHAR"}})
    assert r.facts["c"] == ColumnFacts(nullable=False, lower=1, upper=r.facts["c"].upper)
    assert str(r.facts["c"]) == "an integer ≥ 1"
    assert r.facts["k"].nullable and r.facts["k"].lower is None
    again = sv.Report.from_json(r.to_json())
    assert again.facts == r.facts
    assert {c: str(f) for c, f in again.facts.items()} == {c: str(f) for c, f in r.facts.items()}


def test_nullable_is_one_value_for_facts_and_output():
    """F2: `ColumnFacts.nullable` and `output[c].nullable` agree."""
    t = ibis.table({"a": "int64", "b": "!int64", "s": "string"}, name="t")
    exprs = [
        t.group_by("s").aggregate(n=t.count(), m=t.a.max(), total=t.b.sum()),
        t.select(t.a, x=t.b * 2, y=t.a.fill_null(0), z=t.s.upper()),
    ]
    for e in exprs:
        r = sv.verify(e, requires={"t": [_.a >= 0, _.a < 1000, _.b >= 0, _.b < 1000]})
        assert {c: f.nullable for c, f in r.facts.items()} == {
            c: t.nullable for c, t in r.output.items() if c in r.facts
        }


def test_facts_rest_on_the_stated_preconditions_under_error():
    """F1: with a needed precondition, no fact rests on an inferred bound."""
    sql, req = "select mrr * 12 as arr from s", {"s": ["mrr >= 0"]}
    r = sv.verify(sql, tables=S, requires=req)
    assert r.needs
    alone = sv.verify(sql, tables=S, requires=req, on_inferred="off")
    assert r.facts == alone.facts
    assert r.output == alone.output
    assumed = sv.verify(sql, tables=S, requires=req, on_inferred="ignore")
    assert assumed.facts["arr"].upper < r.facts["arr"].upper


def _as_ensures(c: str, f: ColumnFacts) -> list:
    col = _[c]
    out = [] if f.nullable else [col.notnull()]
    if f.lower is not None:
        out.append(col.isnull() | (col >= f.lower))
    if f.upper is not None:
        out.append(col.isnull() | (col <= f.upper))
    return out


def _cases():
    pytest.importorskip("sverify_dev")
    from sverify_dev.coverage import CASES

    return [c for c in CASES if c.expected == "verified"]


@needs_repo
@pytest.mark.slow
def test_each_fact_is_a_postcondition_that_proves():
    """F3: over the coverage cases, every field of every column's facts
    proves when given as `ensures`."""
    failed = []
    for case in _cases():
        expr = case.build()
        r = sv.verify(expr, counterexamples=0)
        ensures = []
        for c, f in r.facts.items():
            if isinstance(f.lower, float) and not math.isfinite(f.lower):
                failed.append((case.label, c, "an infinite bound"))
            try:
                ensures += _as_ensures(c, f)
            except Exception as e:  # noqa: BLE001 - a bound Ibis cannot write
                failed.append((case.label, c, repr(e)))
        if not ensures:
            continue
        again = sv.verify(expr, ensures=ensures, counterexamples=0)
        failed += [(case.label, e.label, e.why) for e in again.ensures if not e.proved]
    assert not failed, failed

"""The plan digest sinks record is stable across releases (#1485, finding 24)."""

import json
import re

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from _repo import ROOT, needs_repo
from sverify import incremental
from sverify.incremental import plan_digest


def _plan() -> dict:
    t = ibis.table({"k": "int64", "a": "int64"}, name="t")
    report = sv.verify(t.group_by("k").aggregate(total=t.a.sum()))
    assert report.internal_plan is not None
    return json.loads(report.internal_plan)


def test_the_digest_ignores_the_extension_list_and_its_anchors() -> None:
    plan = _plan()
    other = json.loads(json.dumps(plan))
    shift = 1000
    for e in other["extensions"]:
        if "extensionFunction" in e:
            e["extensionFunction"]["functionAnchor"] += shift
    other["extensions"].append(
        {"extensionFunction": {"functionAnchor": 5, "name": "a_function_a_later_release_adds"}}
    )
    other["extensions"].reverse()

    def renumber(node: object) -> None:
        if isinstance(node, dict):
            for k, v in node.items():
                if k == "functionReference":
                    node[k] = v + shift
                else:
                    renumber(v)
        elif isinstance(node, list):
            for v in node:
                renumber(v)

    renumber(other["relations"])
    assert plan_digest(json.dumps(plan)) == plan_digest(json.dumps(other))


def test_the_digest_sees_a_change_of_the_plan() -> None:
    t = ibis.table({"k": "int64", "a": "int64"}, name="t")
    one = sv.verify(t.group_by("k").aggregate(total=t.a.sum())).internal_plan
    two = sv.verify(t.group_by("k").aggregate(total=t.a.max())).internal_plan
    assert one is not None and two is not None
    assert plan_digest(one) != plan_digest(two)


def test_the_digest_is_pinned() -> None:
    """A change to the canonical form fails here, and the release then says
    "this release recomputes sinks"."""
    plan = {
        "extensions": [{"extensionFunction": {"functionAnchor": 7, "name": "sum:i64"}}],
        "relations": [{"root": {"input": {"read": {}}, "functionReference": 7}}],
    }
    # Without `MEANING_CHANGES`: the pin is of the canonical form alone.
    assert plan_digest(json.dumps(plan), ()) == (
        "40387fa8d0c5b97ac7f516e8e7975568d526a328b248d58d9b0f570a5571dcae"
    )


LAST_UNMARKED = 49
"""The highest decision before the `Recomputes sinks:` line."""


def _decisions() -> dict[int, str]:
    record = (ROOT / "docs" / "decisions.md").read_text()
    parts = re.split(r"^### D(\d+)\. ", record, flags=re.M)
    return {int(n): body for n, body in zip(parts[1::2], parts[2::2], strict=True)}


@needs_repo
def test_every_decision_after_the_last_unmarked_says_whether_it_recomputes_sinks() -> None:
    missing = [
        f"D{n}"
        for n, body in _decisions().items()
        if n > LAST_UNMARKED and not re.search(r"^Recomputes sinks: (yes|no)\b", body, flags=re.M)
    ]
    assert not missing, (
        f"{missing} lack a line `Recomputes sinks: yes` or `no` "
        "(a decision that changes a value of the reference or narrows what it allows says yes "
        "and goes into `MEANING_CHANGES`)"
    )


@needs_repo
def test_the_record_of_changes_of_meaning_matches_the_decisions() -> None:
    yes = {
        f"D{n}"
        for n, body in _decisions().items()
        if n > LAST_UNMARKED and re.search(r"^Recomputes sinks: yes\b", body, flags=re.M)
    }
    recorded = {c for c in incremental.MEANING_CHANGES if re.fullmatch(r"D\d+", c)}
    assert yes == recorded, (
        f"decisions that recompute sinks and `MEANING_CHANGES` differ: "
        f"missing from the record {sorted(yes - recorded)}, not a recomputing decision "
        f"{sorted(recorded - yes)}"
    )


def test_a_change_of_meaning_changes_the_digest_and_is_named_on_refresh(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    t = ibis.table({"k": "int64", "a": "int64"}, name="t")
    report = sv.verify(t.group_by("k").aggregate(total=t.a.sum()))
    plan = report.internal_plan
    assert plan is not None
    monkeypatch.setattr(incremental, "MEANING_CHANGES", ())
    assert plan_digest(plan, ()) == plan_digest(plan)
    assert plan_digest(plan, ("D53",)) != plan_digest(plan, ())
    assert plan_digest(plan, ("D53", "#1702")) != plan_digest(plan, ("D53",))

    con = sv.connect()
    con.put("t", pa.table({"k": [1], "a": [2]}))
    view = incremental.Pipeline(con).view("v", t.group_by("k").aggregate(total=t.a.sum()))
    stored = incremental.Stored(
        "x@v0", "x", plan_digest(view.plan, ()), {}, {}, pa.table({"k": [1], "total": [2]})
    )
    assert view._mismatch(stored) != "the plan changed"
    monkeypatch.setattr(incremental, "MEANING_CHANGES", ("D53", "#1702"))
    assert view._mismatch(stored) == "sverify changed what this plan computes (D53, #1702)"
    stored.plan = plan_digest(view.plan, ("D53",))
    assert view._mismatch(stored) == "sverify changed what this plan computes (#1702)"
    stored.plan = "0" * 64
    assert view._mismatch(stored) == "the plan changed"

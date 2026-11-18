"""The plan digest sinks record is stable across releases (#1485, finding 24)."""

import json

import ibis

import sverify as sv
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
    assert plan_digest(json.dumps(plan)) == (
        "40387fa8d0c5b97ac7f516e8e7975568d526a328b248d58d9b0f570a5571dcae"
    )

"""The shims `to_substrait(shims="apply")` writes (#664): rewrites of a
typed plan into well-specified Substrait, one per spec gap the proof meets.

Internal: not part of sverify's public API. `sverify.substrait_export`
types the plan first (`_Typer`), which records the places a shim rewrites:
aggregates, sort fields, casts and calls, each with its argument types. A
shim edits the plan in place and declares the functions it calls by name;
the export then types the whole plan again, which gives every new call its
URN, compound name and output type.

Each shim returns a description for the manifest, or None where it cannot
write the gap away (the export then refuses, or annotates with
`shims="annotate"`):

- ST-3 (`stat_degenerate`): `variance` and `std_dev` of fewer values than
  the distribution needs (two for `SAMPLE`, one for `POPULATION`) are NULL,
  as the reference has them: `if count(x) < n then NULL else variance(x)`.
- ST-4 (`nan_equality`, `nan_order`, `zero_sign` of comparisons, keys and
  sorts): an equality of doubles is `x + 0.0 = y + 0.0 OR (is_nan(x) AND is_nan(y))`; a
  double grouping key is the pair `(is_nan(x), if is_nan(x) then 0.0 else
  x + 0.0)`, and the key comes back as `if k1 then NaN else k2`; a double
  sort key is `is_nan(x)` and then `x + 0.0`, so NaN sorts greatest and the
  two zeros tie. An ordering comparison of doubles (`<`, `>=`, …) has no
  shim yet.
- ST-6 (`float_to_int`): a cast of a double or decimal to an integer
  truncates first, `if x >= 0 then floor(x) else ceil(x)`, so the cast is
  exact.
- ST-8 (`decimal_rescale`): no rewrite; it holds when no decimal `+`, `-`
  or `*` of the plan reduces its scale (the YAML's result type keeps every
  digit), and the export says so.
"""

from __future__ import annotations

import copy
from collections.abc import Callable, Sequence
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from sverify.substrait_export import _Typer

Json = dict[str, Any]

_DOUBLES = frozenset({"fp32", "fp64"})
_ORDERING = frozenset({"lt", "gt", "lte", "gte", "between"})
_EQUALITY = frozenset({"equal", "not_equal"})


class Builder:
    """Declares functions by name in a plan and builds expressions."""

    def __init__(self, plan: Json):
        self.plan = plan
        self.anchors: dict[str, int] = {}

    def fn(self, name: str) -> int:
        if name not in self.anchors:
            used = [
                e["extensionFunction"]["functionAnchor"]
                for e in self.plan.get("extensions", [])
                if "extensionFunction" in e
            ]
            anchor = max(used, default=0) + 1
            self.plan.setdefault("extensions", []).append(
                {"extensionFunction": {"functionAnchor": anchor, "name": name}}
            )
            self.anchors[name] = anchor
        return self.anchors[name]

    def call(self, name: str, *args: Json, options: Sequence[Json] = ()) -> Json:
        f: Json = {
            "functionReference": self.fn(name),
            "arguments": [{"value": a} for a in args],
        }
        if options:
            f["options"] = list(options)
        return {"scalarFunction": f}

    @staticmethod
    def field(i: int) -> Json:
        return {
            "selection": {"directReference": {"structField": {"field": i}}, "rootReference": {}}
        }

    @staticmethod
    def double(v: float | str) -> Json:
        return {"literal": {"fp64": v}}

    @staticmethod
    def if_then(cond: Json, then: Json, other: Json) -> Json:
        return {"ifThen": {"ifs": [{"if": cond, "then": then}], "else": other}}

    def canonical(self, x: Json) -> Json:
        """`x + 0.0`: IEEE 754 makes `-0.0 + 0.0` the positive zero."""
        return self.call("add", copy.deepcopy(x), self.double(0))


def _is_double(t: Any) -> bool:
    return t is not None and getattr(t, "name", None) in _DOUBLES


# -- ST-4 -----------------------------------------------------------------------


def st4(typer: _Typer, b: Builder) -> Json | None:
    """Comparisons, keys and sorts of doubles, with NaN equal to NaN and
    greatest, and one zero (ST-4). None where the plan orders doubles by a
    comparison, which no shim writes yet."""
    if any(c.name in _ORDERING and any(_is_double(a) for a in c.args) for c in typer.calls):
        return None
    done: list[str] = []
    for c in typer.calls:
        if c.name in _EQUALITY and len(c.args) == 2 and all(_is_double(a) for a in c.args):
            x, y = (a["value"] for a in c.node["arguments"])
            eq = b.call("equal", b.canonical(x), b.canonical(y))
            nan = b.call(
                "and", b.call("is_nan", copy.deepcopy(x)), b.call("is_nan", copy.deepcopy(y))
            )
            out = b.call("or", eq, nan)
            if c.name == "not_equal":
                out = b.call("not", out)
            holder = c.holder
            if holder is None:
                return None
            holder.clear()
            holder.update(out)
            done.append(f"{c.name} of doubles: x + 0.0 = y + 0.0 OR (is_nan(x) AND is_nan(y))")
    for s, t in typer.sorts:
        if _is_double(t):
            e = s["expr"]
            first = {"expr": b.call("is_nan", copy.deepcopy(e)), "direction": s["direction"]}
            s["expr"] = b.canonical(e)
            s["_before"] = first
            done.append("sort key of doubles: is_nan(x), then x + 0.0")
    _split_sorts(typer.plan)
    for agg in typer.aggregates:
        if any(_is_double(t) for t in agg.key_types):
            if not _double_keys(agg, b):
                return None
            done.append("grouping key of doubles: (is_nan(x), if is_nan(x) then 0.0 else x + 0.0)")
    return {"shim": "; ".join(dict.fromkeys(done)) or "no double comparison, key or sort"}


def _split_sorts(node: Any) -> None:
    """Put each sort field's `_before` field ahead of it."""
    if isinstance(node, dict):
        for k, v in list(node.items()):
            if k == "sorts" and isinstance(v, list):
                out = []
                for s in v:
                    if isinstance(s, dict) and "_before" in s:
                        out.append(s.pop("_before"))
                    out.append(s)
                node[k] = out
            _split_sorts(node[k])
    elif isinstance(node, list):
        for v in node:
            _split_sorts(v)


def _first_appearance(groupings: Sequence[Json]) -> list[int]:
    order: list[int] = []
    for g in groupings:
        for r in g.get("expressionReferences", []):
            if r not in order:
                order.append(int(r))
    return order


def _double_keys(agg: Any, b: Builder) -> bool:
    body = agg.body
    groupings = body.get("groupings", [])
    if any(g.get("groupingExpressions") for g in groupings):
        return False
    keys = body.get("groupingExpressions", [])
    before = _first_appearance(groupings)
    n_measures = len(body.get("measures", []))
    added: dict[int, int] = {}
    for i, t in enumerate(agg.key_types):
        if not _is_double(t):
            continue
        x = keys[i]
        nan = b.call("is_nan", copy.deepcopy(x))
        keys[i] = b.if_then(copy.deepcopy(nan), b.double(0), b.canonical(x))
        keys.append(nan)
        added[i] = len(keys) - 1
        for g in groupings:
            if i in g.get("expressionReferences", []):
                g["expressionReferences"].append(added[i])
    after = _first_appearance(groupings)
    pos_after = {k: p for p, k in enumerate(after)}
    # The aggregate's columns now, and the expressions that give back the
    # columns it had.
    restore: list[Json] = []
    for k in before:
        if k in added:
            restore.append(
                b.if_then(b.field(pos_after[added[k]]), b.double("NaN"), b.field(pos_after[k]))
            )
        else:
            restore.append(b.field(pos_after[k]))
    restore += [b.field(len(after) + m) for m in range(n_measures)]
    _wrap(agg, len(after) + n_measures, restore)
    return True


def _wrap(agg: Any, width: int, outputs: list[Json]) -> None:
    """Replace the aggregate by a project over it whose outputs are
    `outputs` (over the aggregate's `width` columns), keeping its emit."""
    container, body = agg.container, agg.body
    emit = (body.get("common") or {}).pop("emit", None)
    if not body.get("common"):
        body.pop("common", None)
    mapping = list(range(width, width + len(outputs)))
    if emit is not None:
        mapping = [mapping[i] for i in emit.get("outputMapping", [])]
    container.clear()
    container["project"] = {
        "common": {"emit": {"outputMapping": mapping}},
        "input": {"aggregate": body},
        "expressions": outputs,
    }
    agg.container = container["project"]["input"]


# -- ST-3 -----------------------------------------------------------------------


def st3(typer: _Typer, b: Builder) -> Json | None:
    """`variance` and `std_dev` of too few values are NULL (ST-3)."""
    done = False
    for agg in typer.aggregates:
        body = agg.body
        measures = body.get("measures", [])
        fixes: list[tuple[int, int, int]] = []
        for j, m in enumerate(list(measures)):
            f = m.get("measure", {})
            call = next((c for c in typer.calls if c.node is f), None)
            name = call.name if call is not None else ""
            if name not in ("variance", "std_dev"):
                continue
            dist = "SAMPLE"
            for o in f.get("options", []):
                if o.get("name") == "distribution" and o.get("preference"):
                    dist = o["preference"][0]
            values = [a["value"] for a in f.get("arguments", []) if "value" in a]
            if len(values) != 1:
                return None
            count: Json = {
                "measure": {
                    "functionReference": b.fn("count"),
                    "arguments": [{"value": copy.deepcopy(values[0])}],
                    "invocation": f.get("invocation", "AGGREGATION_INVOCATION_ALL"),
                }
            }
            if "filter" in m:
                count["filter"] = copy.deepcopy(m["filter"])
            measures.append(count)
            fixes.append((j, len(measures) - 1, 2 if dist == "SAMPLE" else 1))
        if not fixes:
            continue
        n_keys = len(_first_appearance(body.get("groupings", [])))
        n_measures = len(measures) - len(fixes)
        outputs: list[Json] = [b.field(k) for k in range(n_keys)]
        need = {j: (c, n) for j, c, n in fixes}
        for j in range(n_measures):
            if j in need:
                c, n = need[j]
                few = b.call("lt", b.field(n_keys + c), {"literal": {"i64": str(n)}})
                null = {"literal": {"null": {"fp64": {"nullability": "NULLABILITY_NULLABLE"}}}}
                outputs.append(b.if_then(few, null, b.field(n_keys + j)))
            else:
                outputs.append(b.field(n_keys + j))
        _wrap(agg, n_keys + len(measures), outputs)
        done = True
    if not done:
        return None
    return {"shim": "variance and std_dev: if count(x) < 2 (1 for POPULATION) then NULL"}


# -- ST-6 -----------------------------------------------------------------------


def st6(typer: _Typer, b: Builder) -> Json | None:
    """Casts to integers truncate first, so the cast is exact (ST-6)."""
    ints = {"i8", "i16", "i32", "i64"}
    n = 0
    for cast, t in typer.casts:
        target = next(iter(cast["type"]))
        if target not in ints or t is None or t.name not in (*_DOUBLES, "decimal"):
            continue
        x = cast["input"]
        zero = b.double(0) if t.name in _DOUBLES else {"literal": {"i64": "0"}}
        cast["input"] = b.if_then(
            b.call("gte", copy.deepcopy(x), zero),
            b.call("floor", copy.deepcopy(x)),
            b.call("ceil", copy.deepcopy(x)),
        )
        n += 1
    if not n:
        return None
    return {"shim": "casts to integers: if x >= 0 then floor(x) else ceil(x), then the cast"}


# -- ST-8 -----------------------------------------------------------------------


def st8(typer: _Typer, b: Builder) -> Json | None:
    """No decimal `+`, `-` or `*` of the plan reduces its scale (ST-8)."""
    for c in typer.calls:
        ds = [a for a in c.args if not isinstance(a, str) and a.name == "decimal"]
        if not ds:
            continue
        if c.name not in ("add", "subtract", "multiply"):
            return None
        scales = [a.params[1] for a in ds]
        exact = max(scales) if c.name != "multiply" else sum(scales)
        if c.resolved.output.name != "decimal" or c.resolved.output.params[1] != exact:
            return None
    return {
        "shim": "none needed: no decimal operation of the plan reduces its scale",
        "rewrite": False,
    }


#: The shims by the option they write away.
SHIMS: dict[str, Callable[[Any, Builder], Json | None]] = {
    "stat_degenerate": st3,
    "nan_equality": st4,
    "nan_order": st4,
    "zero_sign": st4,
    "nan_kind": st4,
    "float_to_int": st6,
    "decimal_rescale": st8,
}

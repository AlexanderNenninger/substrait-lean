"""Lean's expressions in the user's terms (#655): column names for the
positional `$i`, and the Ibis or SQL operator for Lean's (`/.`, `DOUBLE(…)`).

Internal: not part of sverify's public API.

The checker names an operation by `Expr.render` (`SubstraitLean/Pretty.lean`),
where `$i` is the i-th column of the input of the relation the operation is
in. The plan (Substrait protobuf JSON) says which columns each relation's
input has: `columns` walks it, and `user_expr` names `$i` where every
relation that reads all of the expression's columns gives them the same
names. Where it cannot tell, the expression keeps Lean's notation.
"""

from __future__ import annotations

import json
import re
from collections.abc import Mapping
from typing import Any, Literal

from sverify import _plan_read

Dialect = Literal["ibis", "sql"]

#: The relation types whose output is their input's columns, unchanged.
_PASS = ("filter", "sort", "fetch")


def _refs(node: Any, out: set[int]) -> None:
    """The input columns an expression reads (`selection` from the root)."""
    if isinstance(node, dict):
        sel = node.get("selection")
        if isinstance(sel, dict) and "rootReference" in sel:
            f = ((sel.get("directReference") or {}).get("structField") or {}).get("field", 0)
            out.add(int(f))
        for v in node.values():
            _refs(v, out)
    elif isinstance(node, list):
        for v in node:
            _refs(v, out)


def _field(e: Any) -> int | None:
    """The column an expression is, if it is one (through casts)."""
    while isinstance(e, dict) and "cast" in e:
        e = e["cast"].get("input")
    sel = e.get("selection") if isinstance(e, dict) else None
    if isinstance(sel, dict) and "rootReference" in sel:
        return int(((sel.get("directReference") or {}).get("structField") or {}).get("field", 0))
    return None


Seen = list[tuple[list[str | None], set[int], dict[int, list[str]]]]


def columns(plan: Mapping[str, Any]) -> Seen:
    """Each relation that computes expressions, as its input's column names
    (None where unknown), the input columns its expressions read, and, for
    an aggregate, the measures over each column (`sum(x)`)."""
    fns = _plan_read.function_names(plan)
    out: Seen = []

    def emit(rel: dict, names: list[str | None]) -> list[str | None]:
        mapping = ((rel.get("common") or {}).get("emit") or {}).get("outputMapping")
        if mapping is None:
            return names
        return [names[i] if i < len(names) else None for i in mapping]

    def record(inp: list[str | None] | None, exprs: Any, measures=None) -> None:
        reads: set[int] = set()
        _refs(exprs, reads)
        # An input whose names are not known is kept, as `[]`: a relation
        # that reads the columns makes their names ambiguous.
        out.append((inp or [], reads, measures or {}))

    def at(inp: list[str | None] | None, e: Any) -> str | None:
        f = _field(e)
        return inp[f] if inp is not None and f is not None and f < len(inp) else None

    def walk(node: Any) -> list[str | None] | None:
        if not isinstance(node, dict) or len(node) != 1:
            return None
        kind, rel = next(iter(node.items()))
        if not isinstance(rel, dict):
            return None
        if kind == "read":
            names: list[str | None] = list((rel.get("baseSchema") or {}).get("names") or [])
            return emit(rel, names)
        if kind in ("join", "cross"):
            left, right = walk(rel.get("left")), walk(rel.get("right"))
            joined = None if left is None or right is None else left + right
            if "expression" in rel:
                record(joined, rel["expression"])
            return None if joined is None else emit(rel, joined)
        if kind == "set":
            ins = [walk(i) for i in rel.get("inputs") or []]
            return None if not ins or ins[0] is None else emit(rel, ins[0])
        inp = walk(rel.get("input"))
        if kind in _PASS:
            if kind == "filter":
                record(inp, rel.get("condition"))
            elif kind == "sort":
                record(inp, rel.get("sorts"))
            return None if inp is None else emit(rel, inp)
        if kind == "project":
            exprs = rel.get("expressions") or []
            record(inp, exprs)
            if inp is None:
                return None
            return emit(rel, inp + [at(inp, e) for e in exprs])
        if kind == "aggregate":
            measures: dict[int, list[str]] = {}
            for m in rel.get("measures") or []:
                fn = (m or {}).get("measure") or {}
                args = fn.get("arguments") or []
                if len(args) == 1 and (f := _field(args[0].get("value"))) is not None:
                    name = _plan_read.base_name(fns.get(fn.get("functionReference", 0), "?"))
                    measures.setdefault(f, []).append(name)
            record(inp, {k: v for k, v in rel.items() if k != "input"}, measures)
            keys = [at(inp, g) for g in rel.get("groupingExpressions") or []]
            if not rel.get("groupingExpressions"):
                keys = [
                    at(inp, e)
                    for g in rel.get("groupings") or []
                    for e in g.get("groupingExpressions") or []
                ]
            if inp is None:
                return None
            return emit(rel, keys + [None] * len(rel.get("measures") or []))
        # Windows, unnests, extensions: their expressions are read, but what
        # they output is not followed.
        record(inp, {k: v for k, v in rel.items() if k != "input"})
        return None

    text = json.dumps(plan)
    if '"subquery"' in text or '"lambda"' in text:
        # Relations inside expressions are not walked, and a lambda's body
        # numbers its parameters as Lean numbers columns: no name is sure.
        return [([], set(range(10_000)), {})]
    for r in plan.get("relations") or []:
        walk((r.get("root") or {}).get("input") or r.get("rel") or {})
    return out


_FIELD = re.compile(r"\$(\d+)")


def _names(expr: str, seen: Seen) -> tuple[dict[int, str], dict[int, list[str]]] | None:
    """The names of the columns `expr` reads, where every relation that
    reads them all agrees, with that relation's measures."""
    wanted = {int(i) for i in _FIELD.findall(expr)}
    if not wanted:
        return {}, {}
    found: list[tuple[dict[int, str], dict[int, list[str]]]] = []
    for names, reads, measures in seen:
        if not wanted <= reads:
            continue
        if any(i >= len(names) or names[i] is None for i in wanted):
            return None
        found.append(({i: names[i] for i in wanted}, measures))  # type: ignore[misc]
    if not found or any(f[0] != found[0][0] for f in found):
        return None
    return found[0]


#: Lean's binary operators (`Functions.prettyOf`) as the user writes them.
_OPS: dict[Dialect, dict[str, str]] = {
    "ibis": {
        "/.": "/", "/": "//", "/ROUND": "/", "*.": "*", "+.": "+", "-.": "-",
        "%.": "%", "^.": "**", "^": "**", "=": "==", "AND": "&", "OR": "|", "||": "+",
    },
    "sql": {
        "/.": "/", "/ROUND": "/", "*.": "*", "+.": "+", "-.": "-", "%.": "%", "^.": "^",
    },
}  # fmt: skip


def _strip(s: str) -> str:
    """`s` without the parentheses around the whole of it."""
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        for i, c in enumerate(s):
            depth += c == "("
            depth -= c == ")"
            if depth == 0 and i < len(s) - 1:
                return s
        s = s[1:-1]
    return s


def user_expr(expr: str, plan: Mapping[str, Any] | None, dialect: Dialect = "ibis") -> str | None:
    """`expr` (Lean's notation) with column names and the user's operators;
    None where the plan does not say which columns it reads."""
    if plan is None:
        return None
    found = _names(expr, columns(plan))
    if found is None:
        return None
    names, measures = found
    out = expr
    # A bare column an aggregate adds up is named by its measure: `sum(x)`.
    if (m := _FIELD.fullmatch(out)) and len(measures.get(int(m[1]), [])) == 1:
        return f"{measures[int(m[1])][0]}({names[int(m[1])]})"
    out = _FIELD.sub(lambda m: names[int(m[1])], out)
    # Implicit casts the user did not write.
    while (new := re.sub(r"\b(?:DOUBLE|AS_DECIMAL_\d+_\d+)\(([^()]*)\)", r"\1", out)) != out:
        out = new
    out = re.sub(r"(\d)d\b", r"\1", out)
    trunc = r"\b(?:DATE|DAY)_TRUNC_(\w+)\(([^()]*)\)"
    if dialect == "ibis":
        out = re.sub(trunc, lambda m: f"{m[2]}.truncate({m[1].lower()!r})", out)
    else:
        out = re.sub(trunc, lambda m: f"date_trunc('{m[1].lower()}', {m[2]})", out)
    ops = _OPS[dialect]
    pattern = "|".join(re.escape(k) for k in sorted(ops, key=len, reverse=True))
    out = re.sub(rf"(?<= )(?:{pattern})(?= )", lambda m: ops[m[0]], out)
    return _strip(out)

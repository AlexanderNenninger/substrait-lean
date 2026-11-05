"""Findings: what a check found wrong, one per postcondition not proved,
needed precondition, runtime error, broken link or unchecked transform,
each with its code (`explain`), level and place in the file. The text
output prints them; `--format github|sarif|junit` write them in those
formats (#793)."""

from __future__ import annotations

from typing import TYPE_CHECKING, Any

from sverify.cli import _explain

if TYPE_CHECKING:
    from sverify.cli._discover import Checked, Discovery


def line_of(c: Checked) -> int | None:
    """The line of the transform's decorator (or `def`) in its file."""
    code = getattr(getattr(c.transform, "fn", None), "__code__", None)
    return getattr(code, "co_firstlineno", None)


def _finding(c: Checked, code: str, message: str, **extra: Any) -> dict[str, Any]:
    return {
        "code": code,
        "level": _explain.level_of(code),
        "message": message,
        "item": c.name,
        "nodes": c.nodes,
        "line": line_of(c),
        **extra,
    }


def of(c: Checked) -> list[dict[str, Any]]:
    """The findings of one application of a transform."""
    r = c.report
    if r is None:
        return [_finding(c, "timeout", "the time budget ran out while proving it")]
    out = []
    for cond in r.ensures:
        if cond.portable or cond.checked:
            continue
        code = _explain.code_of(cond.reason or "unknown")
        extra: dict[str, Any] = {"condition": cond.label}
        if cond.counterexample is not None:
            extra["counterexample"] = str(cond.counterexample)
        out.append(_finding(c, code, f"ensures {cond.label}: {cond.why}", **extra))
    for n in r.needs:
        text = f"needs {n.code} on {n.table}"
        if n.issue is not None:
            text += f" (else {n.issue.kind} in {n.issue.what})"
        out.append(_finding(c, "needs", text, table=n.table, condition=n.label))
    for i in r.errors:
        extra = {"hint": i.hint} if i.hint else {}
        out.append(_finding(c, _explain.code_of(i.kind), f"may fail: {i.message}", **extra))
    if r.transfer:
        text = f"Substrait allows more at {len(r.transfer)} option(s)"
        out.append(_finding(c, "transfer", text))
    if r.floats_unmet:
        out.append(_finding(c, "floats", r.floats_unmet))
    out += [_finding(c, "composition", m) for m in c.links]
    return out


def passed(c: Checked) -> list[str]:
    """The postconditions proved, as labels: JUnit's passing test cases."""
    if c.report is None:
        return []
    return [cond.label for cond in c.report.ensures if cond.portable]


def unchecked(name: str, d: Discovery) -> dict[str, Any]:
    t = next((t for t in d.transforms.values() if t.name == name), None)
    code = getattr(getattr(t, "fn", None), "__code__", None)
    return {
        "code": "unchecked",
        "level": _explain.level_of("unchecked"),
        "message": "the file never applies it, so it has no inputs to be proved on",
        "item": name,
        "nodes": [],
        "line": getattr(code, "co_firstlineno", None),
    }

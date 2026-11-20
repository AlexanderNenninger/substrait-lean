"""Findings: what a check found wrong, one per postcondition not proved,
needed precondition, runtime error, broken link or unchecked transform,
each with its code (`explain`), level and place in the file. The text
output prints them; `--format github|sarif` write them in those
formats (#793)."""

from __future__ import annotations

from typing import TYPE_CHECKING, Any

from sverify._user_text import plain
from sverify.cli import _explain

if TYPE_CHECKING:
    from sverify.cli._discover import Checked, Discovery
    from sverify.io._common import Drift
    from sverify.io._credentials import CredentialUse


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
    for cond in r._unmet_ensures():
        code = _explain.code_of(cond.reason or "unknown")
        extra: dict[str, Any] = {"condition": cond.label}
        if cond.counterexample is not None:
            extra["counterexample"] = str(cond.counterexample)
        out.append(_finding(c, code, f"{plain(cond.label)}: {cond.why}", **extra))
    for n in r.needs:
        text = f"needs {n.code} on {n.table}"
        if n.issue is not None:
            text += f" (else {n.issue.kind} in {n.issue.what})"
        out.append(_finding(c, "needs", text, table=n.table, condition=n.label))
    for i in r.errors:
        extra = {"hint": i.hint} if i.hint else {}
        out.append(_finding(c, _explain.code_of(i.kind), f"may fail: {i.message}", **extra))
    if r._transfer:
        text = f"Substrait allows more at {len(r._transfer)} option(s)"
        out.append(_finding(c, "transfer", text))
    if r.floats_unmet:
        out.append(_finding(c, "floats", r.floats_unmet))
    out += [_finding(c, "composition", m) for m in c.links]
    return out


def drift(var: str, d: Drift) -> list[dict[str, Any]]:
    """The findings of a stored node's contract against its sink's record
    (`--against-sink`): one `contract_weakened` per committed promise it no
    longer proves, and a `plan_changed` note."""

    def finding(code: str, message: str, condition: str | None = None) -> dict[str, Any]:
        out = {
            "code": code,
            "level": _explain.level_of(code),
            "message": message,
            "item": var,
            "nodes": [var],
            "line": None,
        }
        return out if condition is None else {**out, "condition": condition}

    w = d.weakened
    out = [
        finding(
            "contract_weakened",
            f"the sink promised {c} IS NOT NULL; not proved now",
            f"{c} IS NOT NULL",
        )
        for c in w["not_null"]
    ]
    out += [
        finding(
            "contract_weakened", f"the sink promised CHECK ({t}); {d.why.get(t, 'not proved')}", t
        )
        for t in w["checks"]
    ]
    out += [
        finding(
            "contract_weakened",
            f"the sink promised unique({', '.join(u)}); not proved now",
            f"unique({', '.join(u)})",
        )
        for u in w["unique"]
    ]
    if d.plan_changed:
        old, new = d.profiles
        text = "the plan differs from the one the sink last committed"
        if (old or "reference") != new:
            text += f" (profile {old or 'reference'} then, {new} now)"
        out.append(finding("plan_changed", text))
    return out


def unchecked(name: str, d: Discovery) -> dict[str, Any]:
    t = next((t for t in d.transforms.values() if t.name == name), None)
    code = getattr(getattr(t, "fn", None), "__code__", None)
    return {
        "code": "unchecked",
        "level": _explain.level_of("unchecked"),
        "message": (
            "the file never applies it and declares no schemas, so it has no inputs to be proved on"
        ),
        "item": name,
        "nodes": [],
        "line": getattr(code, "co_firstlineno", None),
    }


def credentials(uses: list[tuple[str, CredentialUse]]) -> list[dict[str, Any]]:
    """The findings of the credentials nodes use: a table outside
    its credential's scope, and credentials given as values."""
    from sverify.io._credentials import INLINE

    out = []
    for var, u in uses:
        if u.in_scope is False:
            text = (
                f"{u.access}s {u.table} ({u.location}) outside what {u.credential} may {u.access}"
            )
            code = "scope"
        elif u.credential == INLINE:
            text = f"{u.table}: credentials given as values; name them (Storage(credentials=...))"
            code = "inline_credentials"
        else:
            continue
        out.append(
            {
                "code": code,
                "level": _explain.level_of(code),
                "message": text,
                "item": var,
                "nodes": [var],
                "line": None,
                "table": u.table,
            }
        )
    return out

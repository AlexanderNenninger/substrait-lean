"""The plain-language contract summary `sverify check` prints first (#744):
what the output guarantees, what each refresh checks on the data, and what
is not proved, in the user's terms, built from a `Report`'s fields."""

from __future__ import annotations

import re
from collections.abc import Collection
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from sverify import Report

_OPS = {"==": "=", "!=": "≠", ">=": "≥", "<=": "≤"}


def plain(label: str) -> str:
    """A condition's label in words: `(_.amount > 10)` is "amount > 10",
    `_.id.notnull()` "id is never NULL", `unique(id)` "no two rows share
    id", `max_rows(10)` "at most 10 rows"."""
    s = label.strip()
    while s.startswith("(") and s.endswith(")") and _balanced(s[1:-1]):
        s = s[1:-1].strip()
    if m := re.fullmatch(r"unique\((.*)\)", s):
        cols = m.group(1)
        return f"no two rows share {cols}" if "," not in cols else f"no two rows share ({cols})"
    if m := re.fullmatch(r"max_rows\((\d+)\)", s):
        return f"at most {int(m.group(1)):,} rows"
    if m := re.fullmatch(r"rows_per\(\[(.*)\], at_most=(\d+)\)", s):
        return f"at most {m.group(2)} rows per {m.group(1)}"
    if m := re.fullmatch(r"references\((\w+), (\w+)\.(\w+)\)", s):
        return f"every {m.group(1)} is a {m.group(3)} of {m.group(2)}"
    if m := re.fullmatch(r"arrives_within\((\w+), (.*)\)", s):
        return f"rows arrive at most {m.group(2)} late by {m.group(1)}"
    s = re.sub(r"_\.(\w+)\.notnull\(\)", r"\1 is never NULL", s)
    s = re.sub(r"_\.(\w+)\.isnull\(\)", r"\1 is NULL", s)
    s = re.sub(r"\b_\.", "", s)
    for op, word in _OPS.items():
        s = s.replace(f" {op} ", f" {word} ")
    return s.replace(" & ", " and ").replace(" | ", " or ")


def _balanced(s: str) -> bool:
    depth = 0
    for ch in s:
        depth += {"(": 1, ")": -1}.get(ch, 0)
        if depth < 0:
            return False
    return depth == 0


def summary(report: Report, sources: Collection[str] | None = None) -> dict[str, list[str]]:
    """What a report's contract means for the data, in words:

    * `guarantees`: what every output row (or the output) meets, proved;
    * `checks`: what each refresh checks on the data before it writes (the
      preconditions on the sources, postconditions checked on the output,
      sums assumed to fit). With `sources`, only the preconditions on
      those tables: the others follow from what the transforms feeding
      them guarantee;
    * `refused`: what is not proved, and the runtime errors it may raise.
    """
    guarantees = [plain(c.label) for c in report.ensures if c.proved and not c.ignores]
    if report.rows is not None:
        guarantees.append(f"at most {report.rows:,} rows")
    checks: list[str] = []
    needed: dict[str, list[str]] = {}
    for n in report.needs:
        needed.setdefault(n.table, []).append(n.label)
    for table, conds in report.requires.items():
        if sources is not None and table not in sources:
            continue
        checks += [f"{table}: {plain(c)}" for c in conds if c not in needed.get(table, ())]
    checks += [f"output: {plain(c.label)}" for c in report.ensures if c.checked]
    checks += [f"while it runs: {i.assumption}" for i in report.assumed]
    refused = [
        f"{plain(c.label)}: not proved, {c.why}"
        for c in report.ensures
        if not c.portable and not c.checked
    ]
    refused += [f"{n.table} needs {plain(n.label)} ({_needed_why(n)})" for n in report.needs]
    refused += [f"may fail: {i.message}" for i in report.errors]
    if report._transfer:
        refused.append(f"Substrait allows more at {len(report._transfer)} option(s)")
    if report.floats_unmet:
        refused.append(f"doubles: {report.floats_unmet}")
    return {"guarantees": guarantees, "checks": checks, "refused": refused}


def _needed_why(n: Any) -> str:
    issue = n.issue
    return f"or {issue.kind} in {issue.what}" if issue is not None else "inferred"

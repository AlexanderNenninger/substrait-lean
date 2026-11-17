"""Written SQL raises at run time only for an issue the checker reports for
that plan (S9a): every guard (`Dialect.raise_`) names the `Issue` it enforces
(`GuardIssue`), and each coverage case whose SQL holds a guard has that issue
among those `substrait-check --contract` reports for the plan. A raise the
report does not state is a wrong verdict, whatever the proof says."""

from __future__ import annotations

import json
import re
from typing import get_args

import pytest

from _repo import ROOT, needs_repo
from sverify import profiles
from sverify._checker import run_checker
from sverify.errors import UnsupportedError
from sverify.sql import to_sql
from sverify.sql.core import Dialect, GuardIssue
from sverify_dev.coverage import CASES, Case, written

#: `Issue.kind`'s text for each constructor (`core/Sverify/Core/Issue.lean`).
KIND = {
    "divByZero": "division by zero",
    "overflow": "overflow",
    "badCast": "cast out of range",
    "negExponent": "negative exponent",
    "badRegex": "invalid regular expression",
    "wraps": "overflow",
    "sumWraps": "SUM overflow",
    "domain": "domain error",
    "raised": "raised by a guard",
    "infinite": "overflow to infinity",
}


@needs_repo
def test_guard_issues_are_leans_constructors() -> None:
    src = (ROOT / "core/Sverify/Core/Issue.lean").read_text()
    body = src[src.index("inductive Issue where") :]
    body = body[: body.index("\n\n", body.index("| infinite"))]
    ctors = re.findall(r"^  \| (\w+)", body, re.M)
    assert set(get_args(GuardIssue)) == set(ctors) | {"asciiOnly"}
    assert set(KIND) == set(ctors)


def _recording(monkeypatch: pytest.MonkeyPatch, used: set[str]) -> None:
    """Record the issue of every guard any dialect writes."""
    seen: set[type] = set()

    def wrap(cls: type) -> None:
        if cls in seen or "raise_" not in vars(cls):
            return
        seen.add(cls)
        orig = vars(cls)["raise_"]

        def raise_(self, message, dep, kind, issue, _orig=orig):  # type: ignore[no-untyped-def]
            used.add(issue)
            return _orig(self, message, dep, kind, issue)

        monkeypatch.setattr(cls, "raise_", raise_)

    def walk(cls: type) -> None:
        wrap(cls)
        for sub in cls.__subclasses__():
            walk(sub)

    walk(Dialect)


def _reported(plan: str) -> set[str]:
    code, out, _ = run_checker(
        ("--contract",), json.dumps({"transform": json.loads(plan), "ensures": []})
    )
    report = json.loads(out)
    return {i["kind"] for i in report.get("issues", [])}


def _guards_of(plan: str, monkeypatch: pytest.MonkeyPatch) -> set[str]:
    used: set[str] = set()
    with monkeypatch.context() as m:
        _recording(m, used)
        for plugin in profiles.plugins().values():
            if plugin.dialect is None:
                continue
            try:
                to_sql(json.loads(plan), plugin.dialect())
            except UnsupportedError:
                continue
    return used


@pytest.mark.parametrize("c", [c for c in CASES if c.expected == "verified"], ids=lambda c: c.label)
def test_written_guards_are_reported_issues(c: Case, monkeypatch: pytest.MonkeyPatch) -> None:
    try:
        plan = written(c)
    except UnsupportedError:
        pytest.skip("not written")
    guards = _guards_of(plan, monkeypatch) - {"asciiOnly"}
    if not guards:
        return
    reported = _reported(plan)
    missing = {g for g in guards if KIND[g] not in reported}
    assert not missing, (
        f"guards {sorted(missing)} are not among the reported issues {sorted(reported)}"
    )


@pytest.mark.xfail(strict=True, reason="#1506: the ASCII guard is not an issue Safety reports")
def test_the_ascii_guard_is_an_issue(monkeypatch: pytest.MonkeyPatch) -> None:
    import ibis

    from sverify.engine import written_plan
    from sverify.ibis_substrait import to_substrait_json

    t = ibis.table({"s": "string"}, name="t")
    plan = written_plan(to_substrait_json(t.select(u=t.s.upper())))
    assert "asciiOnly" not in _guards_of(plan, monkeypatch) or _reported(plan)

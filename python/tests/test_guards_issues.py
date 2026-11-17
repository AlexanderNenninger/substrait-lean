"""Written SQL raises at run time only for an issue the checker reports for
that plan (S9a): every guard (`Dialect.raise_`) names the `Issue` it enforces
(`GuardIssue`), and each coverage case whose SQL holds a guard has that issue
among those `substrait-check --contract` reports for the plan. A raise the
report does not state is a wrong verdict, whatever the proof says.

The rule (S9a-1): on input the report admits, written SQL raises only for an
issue the report lists. A guard on an issue the checker discharged (a column's
type, a literal argument) cannot fire and may stay, so each plan is written a
second time with the report's `unchecked` slots, and the guards left there must
be reported (a). A slot where Safety models no issue is unchecked, so (a) alone
passes a guard Safety does not model; (b) asks that each guard site survives
the unchecked writing, with its issue reported, in at least one plan."""

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


import functools
import sys
from collections import defaultdict

Site = tuple[str, int, str]  # (file, line, issue)


def _recording(monkeypatch: pytest.MonkeyPatch, used: set[Site]) -> None:
    """Record the call site and issue of every guard any dialect writes."""
    seen: set[type] = set()

    def wrap(cls: type) -> None:
        if cls in seen or "raise_" not in vars(cls):
            return
        seen.add(cls)
        orig = vars(cls)["raise_"]

        def raise_(self, message, dep, kind, issue, _orig=orig):  # type: ignore[no-untyped-def]
            f = sys._getframe(1)
            used.add((f.f_code.co_filename.split("/src/")[-1], f.f_lineno, issue))
            return _orig(self, message, dep, kind, issue)

        monkeypatch.setattr(cls, "raise_", raise_)

    def walk(cls: type) -> None:
        wrap(cls)
        for sub in cls.__subclasses__():
            walk(sub)

    walk(Dialect)


def _report(plan: str) -> dict:
    code, out, _ = run_checker(
        ("--contract",), json.dumps({"transform": json.loads(plan), "ensures": []})
    )
    return json.loads(out)


def _kinds(report: dict) -> set[str]:
    return {i["kind"] for i in report.get("issues", [])}


def _sites(plan: str, unchecked: dict | None, monkeypatch: pytest.MonkeyPatch) -> set[Site]:
    used: set[Site] = set()
    with monkeypatch.context() as m:
        _recording(m, used)
        for plugin in profiles.plugins().values():
            if plugin.dialect is None:
                continue
            try:
                to_sql(json.loads(plan), plugin.dialect(), unchecked=unchecked)
            except UnsupportedError:
                continue
    return used


@functools.cache
def _scan(label: str) -> tuple[frozenset[Site], frozenset[Site], frozenset[str]] | None:
    """The guard sites of case `label` as written, as written with the report's
    unchecked slots, and the kinds the report lists."""
    c = next(c for c in CASES if c.label == label)
    try:
        plan = written(c)
    except UnsupportedError:
        return None
    mp = pytest.MonkeyPatch()
    try:
        full = _sites(plan, None, mp)
        if not full:
            return frozenset(), frozenset(), frozenset()
        report = _report(plan)
        left = _sites(plan, report.get("unchecked"), mp)
        return frozenset(full), frozenset(left), frozenset(_kinds(report))
    finally:
        mp.undo()


VERIFIED = [c for c in CASES if c.expected == "verified"]


@pytest.mark.parametrize("c", VERIFIED, ids=lambda c: c.label)
def test_the_guards_left_unchecked_are_reported(c: Case) -> None:
    """(a): every guard the unchecked writing keeps has its issue reported."""
    scan = _scan(c.label)
    if scan is None:
        pytest.skip("not written")
    _, left, kinds = scan
    missing = sorted(
        (f"{f}:{n}", g) for f, n, g in left if g != "asciiOnly" and KIND[g] not in kinds
    )
    assert not missing, f"guards without a reported issue {sorted(kinds)}: {missing}"


def test_every_guard_site_is_reported_somewhere() -> None:
    """(b): each guard site survives the unchecked writing, with its issue
    reported, in some plan: a witness for a site no case reaches."""
    sites: dict[tuple[str, int], set[str]] = defaultdict(set)
    proven: set[tuple[str, int]] = set()
    for c in VERIFIED:
        scan = _scan(c.label)
        if scan is None:
            continue
        full, left, kinds = scan
        for f, n, g in full:
            sites[(f, n)].add(g)
        for f, n, g in left:
            if KIND.get(g) in kinds:
                proven.add((f, n))
    proven |= set(WITNESSES)
    lost = sorted((f"{f}:{n}", sorted(g)) for (f, n), g in sites.items() if (f, n) not in proven)
    assert not [x for x in lost if "asciiOnly" not in x[1]], f"sites with no witness: {lost}"


#: Witness plans for guard sites no case reaches: `{(file, line): plan}`.
WITNESSES: dict[tuple[str, int], str] = {}


@pytest.mark.xfail(strict=True, reason="#1506: the ASCII guard is not an issue Safety reports")
def test_the_ascii_guard_is_an_issue(monkeypatch: pytest.MonkeyPatch) -> None:
    import ibis

    from sverify.engine import written_plan
    from sverify.ibis_substrait import to_substrait_json

    t = ibis.table({"s": "string"}, name="t")
    plan = written_plan(to_substrait_json(t.select(u=t.s.upper())))
    assert "asciiOnly" not in {g for *_, g in _sites(plan, None, monkeypatch)}

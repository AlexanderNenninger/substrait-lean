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

import functools
import json
import re
import sys
from collections.abc import Callable
from typing import get_args

import ibis
import pyarrow as pa
import pytest

from _repo import ROOT, needs_repo
from sverify import profiles
from sverify._checker import run_checker
from sverify.engine import connect, put_table, substrait_json, written_plan
from sverify.errors import UnsupportedError
from sverify.ibis_substrait import to_substrait_json
from sverify.sql import to_sql
from sverify.sql.core import UNISSUED, Dialect, GuardIssue
from sverify_dev.coverage import CASES, Case, written
from sverify_dev.coverage_cases._common import t

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
    "nonAscii": "non-ASCII text",
}


@needs_repo
def test_guard_issues_are_leans_constructors() -> None:
    src = (ROOT / "core/Sverify/Core/Issue.lean").read_text()
    body = src[src.index("inductive Issue where") :]
    body = body[: body.index("\n\n", body.index("| infinite"))]
    ctors = re.findall(r"^  \| (\w+)", body, re.M)
    assert set(get_args(GuardIssue)) == set(ctors) | UNISSUED
    assert set(KIND) == set(ctors)


Site = tuple[str, int, str, str]  # (file, line, issue, message)


def _recording(monkeypatch: pytest.MonkeyPatch, used: set[Site]) -> None:
    """Record the call site, issue and message of every guard any dialect writes."""
    seen: set[type] = set()

    def wrap(cls: type) -> None:
        if cls in seen or "raise_" not in vars(cls):
            return
        seen.add(cls)
        orig = vars(cls)["raise_"]

        def raise_(self, message, dep, kind, issue, _orig=orig):  # type: ignore[no-untyped-def]
            f = sys._getframe(1)
            file = re.split(r"/(?:src|site-packages)/", f.f_code.co_filename)[-1]
            used.add((file, f.f_lineno, issue, message))
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
def _scan(plan: str) -> tuple[frozenset[Site], frozenset[Site], frozenset[str]]:
    """The guard sites of `plan` as written, as written with the report's
    unchecked slots, and the kinds the report lists."""
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


def _case_scan(c: Case) -> tuple[frozenset[Site], frozenset[Site], frozenset[str]] | None:
    try:
        return _scan(written(c))
    except UnsupportedError:
        return None


VERIFIED = [c for c in CASES if c.expected == "verified"]

#: The guards a case's unchecked writing keeps although the report lists no
#: issue of their kind, `{case: {(file, issue, message): (class, cause)}}`.
#: Dead: no input the report admits fires it (the marks do not reach its slot,
#: or the writer keeps it without them). Live: DuckDB raises on admitted
#: input, a wrong verdict (S9, none today). The assertion is equality, so a
#: new unreported guard and a closed gap both fail.
KNOWN: dict[str, dict[tuple[str, str, str], tuple[str, str]]] = {
    "arithmetic over aggregates": {
        ("sverify/sql/core/_base.py", "domain", "domain error"): (
            "dead",
            "the operands are sums and extrema of integers, converted to doubles: never infinite",
        ),
        ("sverify_duckdb/dialect.py", "domain", "domain error"): (
            "dead",
            "the lowered division template's infinity check, over the same finite operands",
        ),
    },
    "scalar subquery": {
        ("sverify/sql/core/_base.py", "domain", "domain error"): (
            "dead",
            "the mean is over an int64 column: its values are finite, so no +inf with -inf",
        ),
        ("sverify/sql/core/_base.py", "infinite", "overflow to infinity"): (
            "dead",
            "the sum of at most 2**63-magnitude values per row cannot reach infinity",
        ),
    },
    "float division": {
        ("sverify/sql/core/_base.py", "infinite", "overflow to infinity"): (
            "dead",
            "an int64 column over the literal 2: finite, and the quotient is smaller",
        ),
    },
    "abs": {
        ("sverify/sql/core/_base.py", "divByZero", "division by zero"): (
            "dead",
            "the negating branch divides by the literal -1",
        ),
        ("sverify_duckdb/dialect.py", "divByZero", "division by zero"): (
            "dead",
            "the lowered template of the same division by the literal -1",
        ),
    },
    "join": {
        ("sverify/sql/snowflake.py", "wraps", "integer overflow"): (
            "dead",
            "the sum of the literal separator's length and 1 in Snowflake's NUMBER arithmetic",
        ),
    },
    "date from columns": {
        (
            "sverify/sql/core/_base.py",
            "raised",
            "make_date of a date outside the calendar or the years 1 to 9999",
        ): ("dead", "the year is the literal 2024, the month is clipped to 1..12, the day is 1"),
    },
}


def _plan(expr: ibis.Table) -> str:
    return written_plan(to_substrait_json(expr))


def _sql_plan(sql: str, semantics: str = "duckdb") -> str:
    """The plan of DuckDB's `sql` over the cases' table `t`, as written."""
    con = connect()
    put_table(con, "t", pa.table(t.schema().to_pyarrow().empty_table()))
    return written_plan(substrait_json(con, sql, semantics=semantics))


#: Plans for the guard sites no case reaches: a divisor that is a column, an
#: operand whose bounds Safety does not get from its type (a timestamp from an
#: integer column, a date from columns), an offset computed from a column.
WITNESSES: dict[str, Callable[[], str]] = {
    "integer division by a column": lambda: _sql_plan("SELECT qty // id AS x FROM t", "reference"),
    "integer modulo by a column": lambda: _plan(t.select(x=t.qty % t.id)),
    "date from unbounded columns": lambda: _plan(t.select(x=ibis.date(t.id, t.qty, t.qty))),
    "substring at an offset from a column, in Ibis": lambda: _plan(
        t.select(x=t.name.substr(t.qty))
    ),
    "months added to a timestamp": lambda: _plan(t.select(x=t.ts + ibis.interval(months=1))),
    "substring at an offset from a column": lambda: _sql_plan(
        "SELECT substr(name, qty) AS x FROM t", "reference"
    ),
    "bucket of a computed timestamp": lambda: _plan(
        t.select(x=(t.ts + ibis.interval(days=1)).bucket(minutes=15))
    ),
    "date_trunc of ts + interval": lambda: _plan(
        t.select(x=(t.ts + ibis.interval(days=1)).truncate("M"))
    ),
    "year of an int timestamp": lambda: _plan(t.select(x=t.qty.as_timestamp("s").year())),
}


def _unreported(scan: tuple[frozenset[Site], frozenset[Site], frozenset[str]]) -> dict:
    _, left, kinds = scan
    return {
        (f, g, m): None for f, _, g, m in sorted(left) if g not in UNISSUED and KIND[g] not in kinds
    }


@pytest.mark.parametrize("c", VERIFIED, ids=lambda c: c.label)
def test_the_guards_left_unchecked_are_reported(c: Case) -> None:
    """(a): every guard the unchecked writing keeps has its issue reported,
    except the ones `KNOWN` classes."""
    scan = _case_scan(c)
    if scan is None:
        pytest.skip("not written")
    kinds = sorted(scan[2])
    got = sorted(_unreported(scan))
    assert set(got) == set(KNOWN.get(c.label, {})), f"reported issues {kinds}: {got}"


@functools.cache
def _witness(name: str) -> str:
    return WITNESSES[name]()


def test_every_guard_site_is_reported_somewhere() -> None:
    """(b): each guard site survives the unchecked writing, with its issue
    reported, in some plan: a case's, or a witness (`WITNESSES`)."""
    sites: set[tuple[str, int]] = set()
    proven: set[tuple[str, int]] = set()
    scans = [s for c in VERIFIED if (s := _case_scan(c)) is not None]
    scans += [_scan(_witness(n)) for n in WITNESSES]
    for full, left, kinds in scans:
        sites |= {(f, n) for f, n, g, _ in full if g not in UNISSUED}
        proven |= {(f, n) for f, n, g, _ in left if KIND.get(g) in kinds}
    lost = sorted(sites - proven)
    assert not lost, f"guard sites no plan reports: {lost}"


@pytest.mark.parametrize("name", WITNESSES)
def test_a_witness_reaches_a_site(name: str) -> None:
    full, left, kinds = _scan(_witness(name))
    assert any(KIND.get(g) in kinds for _, _, g, _ in left), (name, sorted(kinds))

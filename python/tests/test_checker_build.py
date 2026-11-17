"""Which build the checker is (`substrait-check --build`): a report says
whether the generated proofs behind it were checked (#1484)."""

from __future__ import annotations

import json
import stat
from pathlib import Path

import ibis
import pytest
from ibis import _

import sverify as sv
from sverify import _checker
from sverify.report import UNCHECKED_CHECKER, Report

orders = ibis.table({"id": "int64", "total": "int64"}, name="orders")
BOUNDED = {"orders": [_.total >= 0, _.total < 1000, sv.unique("id")]}


def _verify(monkeypatch: pytest.MonkeyPatch, answer: bool | None) -> Report:
    monkeypatch.setattr(_checker, "_generated_proofs", lambda path: answer)
    monkeypatch.setenv("SVERIFY_CACHE", "off")
    _checker._run_checker.cache_clear()
    return sv.verify(
        orders.select("id", d=_.total * 2), requires=BOUNDED, ensures=[_.d >= 0, sv.unique("id")]
    )


def test_checked_build(monkeypatch: pytest.MonkeyPatch) -> None:
    report = _verify(monkeypatch, True)
    assert report.proved and str(report).splitlines()[0] == "proved"
    assert json.loads(report.to_json())["checker"] == {"generated_proofs": True}


def test_unchecked_build_names_itself(monkeypatch: pytest.MonkeyPatch) -> None:
    report = _verify(monkeypatch, False)
    assert report.proved and report.verdict == "proved"
    assert str(report).splitlines()[0] == "proved" + UNCHECKED_CHECKER
    back = Report.from_json(report.to_json())
    assert str(back).splitlines()[0] == "proved" + UNCHECKED_CHECKER
    assert json.loads(back.to_json())["checker"] == {"generated_proofs": False}


def test_unknown_build_is_null(monkeypatch: pytest.MonkeyPatch) -> None:
    report = _verify(monkeypatch, None)
    assert str(report).splitlines()[0] == "proved"
    assert json.loads(report.to_json())["checker"] == {"generated_proofs": None}


def test_report_without_the_field_reads() -> None:
    """A report an earlier 1.x wrote has no `checker` key."""
    doc = json.loads(
        sv.verify(orders.select("id"), requires=BOUNDED, ensures=[sv.unique("id")]).to_json()
    )
    del doc["checker"]
    assert Report.from_json(doc)._generated_proofs is None


def _fake(tmp_path: Path, text: str) -> str:
    path = tmp_path / "substrait-check"
    path.write_text(f"#!/bin/sh\necho '{text}'\n")
    path.chmod(path.stat().st_mode | stat.S_IEXEC)
    return str(path)


@pytest.mark.parametrize(
    ("text", "want"),
    [
        ("generated proofs checked", True),
        ("generated proofs unchecked", False),
        ("something else", None),
    ],
)
def test_reads_the_build_once_per_binary(tmp_path: Path, text: str, want: bool | None) -> None:
    path = _fake(tmp_path, text)
    _checker._generated_proofs.cache_clear()
    assert _checker._generated_proofs(path) is want
    assert _checker._generated_proofs(path) is want
    assert _checker._generated_proofs.cache_info().hits == 1


def test_missing_binary_is_unknown(tmp_path: Path) -> None:
    _checker._generated_proofs.cache_clear()
    assert _checker._generated_proofs(str(tmp_path / "nope")) is None

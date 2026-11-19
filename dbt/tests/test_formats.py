"""`sverify-dbt check --format github|sarif|junit` (#891)."""

from __future__ import annotations

import json
import xml.etree.ElementTree as ET

from sverify_dbt import formats
from sverify_dbt.cli import BUDGET, main
from sverify_dbt.result import CheckResult, ContractIssue, ModelResult, TestResult


def _result() -> CheckResult:
    def t(
        label: str, status: str, why: str | None = None, counterexample: str | None = None
    ) -> TestResult:
        return TestResult(None, None, label, "test", status, why, counterexample)

    ok = ModelResult("ok", "model.p.ok", "models/ok.sql", "ref('ok')")
    ok.tests = [t("unique(id)", "proved")]
    bad = ModelResult("bad", "model.p.bad", "models/bad.sql", "ref('bad')")
    bad.tests = [
        t("not_null(x)", "not proved", why="a row may be NULL", counterexample="x = NULL"),
        t("unique(y)", "not checked", why="the model was refused"),
    ]
    bad.contract = [ContractIssue("z", "declared int, found text")]
    refused = ModelResult(
        "rec", "model.p.rec", "models/rec.sql", "ref('rec')", refused="no WITH RECURSIVE"
    )
    return CheckResult("p", "/p", [ok, bad, refused], {})


def test_github_has_one_annotation_per_finding() -> None:
    lines = formats.github(_result()).splitlines()
    assert len(lines) == 4
    assert lines[0].startswith("::error file=models/bad.sql,title=sverify contract_mismatch")
    assert any("counterexample: x = NULL" in line.replace("%0A", "\n") for line in lines)
    assert any(line.startswith("::warning file=models/rec.sql") for line in lines)


def test_sarif_is_a_log_with_a_result_per_finding() -> None:
    log = json.loads(formats.sarif(_result(), "1.0"))
    run = log["runs"][0]
    assert log["version"] == "2.1.0" and len(run["results"]) == 4
    assert {r["ruleId"] for r in run["results"]} <= {
        r["id"] for r in run["tool"]["driver"]["rules"]
    }
    uris = {
        r["locations"][0]["physicalLocation"]["artifactLocation"]["uri"] for r in run["results"]
    }
    assert uris == {"models/bad.sql", "models/rec.sql"}


def test_junit_fails_what_is_not_proved_and_skips_what_is_not_checked() -> None:
    root = ET.fromstring(formats.junit(_result()))
    suites = {s.get("name"): s for s in root}
    assert suites["ok"].get("failures") == "0"
    assert suites["bad"].get("failures") == "2" and suites["bad"].get("skipped") == "1"
    assert suites["rec"].get("skipped") == "1"


def test_a_check_past_its_time_budget_exits_4(tmp_path, monkeypatch, capsys) -> None:
    from sverify.cli import _limits

    def slow(*args: object, **kw: object) -> None:
        raise _limits.BudgetExceeded("time", "1 s")

    monkeypatch.setattr("sverify_dbt.cli.check", slow)
    assert main(["check", str(tmp_path), "--timeout", "1"]) == BUDGET
    assert "time budget exceeded" in capsys.readouterr().err


def test_a_bad_memory_limit_is_a_usage_error(tmp_path, capsys) -> None:
    assert main(["check", str(tmp_path), "--memory-limit", "lots"]) == 2
    assert "memory limit" in capsys.readouterr().err

"""`sverify-dbt check`'s exit codes and what gates them (#891, 1.2, 1.3)."""

from __future__ import annotations

import pytest
from sverify.errors import UnsupportedError

from sverify_dbt import cli
from sverify_dbt.cli import main
from sverify_dbt.result import CheckResult, ContractIssue, ModelResult, TestResult


def _t(label: str, status: str, kind: str = "test") -> TestResult:
    return TestResult(None, None, label, kind, status)


def _project(**models: ModelResult) -> CheckResult:
    return CheckResult("p", "/p", list(models.values()), {})


def _model(name: str) -> ModelResult:
    return ModelResult(name, f"model.p.{name}", f"models/{name}.sql", f"ref('{name}')")


def _refused() -> ModelResult:
    m = _model("rec")
    m.constraints = [_t("primary_key(id)", "pending", "constraint")]
    return m.refuse("no WITH RECURSIVE")


def _run(monkeypatch: pytest.MonkeyPatch, result: CheckResult, *flags: str) -> int:
    monkeypatch.setattr(cli, "check", lambda *a, **k: result)
    return main(["check", ".", *flags])


def test_a_refused_model_with_an_enforced_contract_fails_the_default_gate(monkeypatch, capsys):
    rec = _refused()
    rec.enforced = True
    result = _project(rec=rec)
    assert _run(monkeypatch, result) == cli.NOT_PROVED
    captured = capsys.readouterr()
    assert "refused: no WITH RECURSIVE" in captured.out and "primary_key(id)" in captured.out
    assert "rec has an enforced contract" in captured.err and "no WITH RECURSIVE" in captured.err
    assert _run(monkeypatch, result, "--fail-on", "never") == 0


def test_a_refused_model_without_a_contract_does_not_fail_the_default_gate(monkeypatch):
    assert _run(monkeypatch, _project(rec=_model("rec").refuse("no WITH RECURSIVE"))) == 0


def test_refused_models_gate_only_where_asked(monkeypatch):
    result = _project(rec=_model("rec").refuse("no WITH RECURSIVE"))
    assert _run(monkeypatch, result, "--fail-on", "unproved") == 0
    assert _run(monkeypatch, result, "--fail-on", "refused") == cli.REFUSED


def test_an_unproved_test_fails_unproved_with_1(monkeypatch):
    m = _model("bad")
    m.tests = [_t("not_null(x)", "not proved")]
    result = _project(bad=m)
    assert _run(monkeypatch, result) == 0
    assert _run(monkeypatch, result, "--fail-on", "unproved") == cli.NOT_PROVED
    both = _project(bad=m, rec=_refused())
    # `refused` includes `unproved`: the unproved test comes first, as exit 1.
    assert _run(monkeypatch, both, "--fail-on", "refused") == cli.NOT_PROVED
    plain = _project(rec=_model("rec").refuse("x"))
    assert _run(monkeypatch, plain, "--fail-on", "refused") == cli.REFUSED
    assert _run(monkeypatch, both, "--fail-on", "unproved") == cli.NOT_PROVED


def test_a_contract_mismatch_and_an_unproved_constraint_fail_the_default_gate(monkeypatch):
    m = _model("c")
    m.contract = [ContractIssue("z", "declared int, found text")]
    assert _run(monkeypatch, _project(c=m)) == cli.NOT_PROVED
    k = _model("k")
    k.constraints = [_t("not_null(x)", "not proved", "constraint")]
    assert _run(monkeypatch, _project(k=k)) == cli.NOT_PROVED
    assert _run(monkeypatch, _project(k=k), "--fail-on", "never") == 0


@pytest.mark.parametrize(
    ("error", "code"),
    [
        (UnsupportedError("not readable"), cli.REFUSED),
        (ValueError("no model named x"), cli.USAGE),
        (FileNotFoundError("substrait-check is missing"), cli.ERROR),
        (RuntimeError("the checker died"), cli.ERROR),
    ],
)
def test_failures_have_sverifys_exit_codes_and_no_traceback(monkeypatch, capsys, error, code):
    def boom(*args: object, **kw: object) -> None:
        raise error

    monkeypatch.setattr(cli, "check", boom)
    assert main(["check", "."]) == code
    assert capsys.readouterr().err.startswith("sverify-dbt:")


def test_a_constraint_sverify_did_not_check_on_a_read_model_still_fails_the_gate(monkeypatch):
    """Only a refused model's constraints are excused: one that sverify could not
    read the condition of, on a model that was checked, is not a pass."""
    m = _model("k")
    m.constraints = [_t("check(x > 0)", "not checked", "constraint")]
    assert _run(monkeypatch, _project(k=m)) == cli.NOT_PROVED

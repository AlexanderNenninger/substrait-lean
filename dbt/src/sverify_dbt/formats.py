"""`sverify-dbt check` for CI systems (#891): GitHub's workflow commands,
SARIF 2.1.0 and JUnit XML. Each is a view of the same findings: one per
unproved test or constraint, per refused model and per contract mismatch."""

from __future__ import annotations

import json
from typing import Any
from xml.sax.saxutils import escape, quoteattr

from sverify.cli import _explain

from sverify_dbt.result import CheckResult, ModelResult

SARIF_SCHEMA = "https://json.schemastore.org/sarif-2.1.0.json"
INFO_URI = "https://github.com/AlexanderNenninger/substrait-lean"
_GITHUB_LEVEL = {"error": "error", "warning": "warning", "note": "notice"}


def findings(result: CheckResult) -> list[dict[str, Any]]:
    """What is wrong with the project, one dict per finding: `file` (the
    model's file), `code` (sverify's, `sverify explain CODE`), `level`,
    `item`, `message`, `nodes` and `line` (None), as `cli.schema.json` has them."""
    out: list[dict[str, Any]] = []
    for m in result.models:
        file = m.path or m.ref
        if m.refused:
            out.append(_f(m, file, "unsupported", "warning", m.name, f"refused: {m.refused}"))
        for issue in m.contract or []:
            item = f"{m.name}.{issue.column}"
            out.append(_f(m, file, "contract_mismatch", "error", item, issue.problem))
        for t in m.tests + m.constraints:
            if t.status == "proved":
                continue
            checked = t.status == "not proved"
            code = t.reason or ("may_be_false" if t.counterexample else "unknown")
            code = code if checked else "unchecked"
            f = _f(m, file, code, "error" if checked else "warning", t.label, _text(t))
            if t.counterexample:
                f["counterexample"] = t.counterexample
            out.append(f)
    return out


def _f(m: ModelResult, file: str, code: str, level: str, item: str, message: str) -> dict[str, Any]:
    return {
        "file": file,
        "code": code,
        "level": level,
        "message": message,
        "item": item,
        "nodes": [m.name],
        "line": None,
    }


def _text(t: Any) -> str:
    return f"{t.status}: {t.label}" + (f": {t.why}" if t.why else "")


def _escape_data(s: str) -> str:
    return s.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


def _escape_property(s: str) -> str:
    return _escape_data(s).replace(":", "%3A").replace(",", "%2C")


def github(result: CheckResult) -> str:
    """One workflow command per finding: `::error file=models/x.sql,title=…::…`."""
    lines = []
    for f in findings(result):
        title = _escape_property(f"sverify {f['code']}: {f['item']}")
        text = f["message"] + (
            f"\ncounterexample: {f['counterexample']}" if "counterexample" in f else ""
        )
        props = f"file={_escape_property(f['file'])},title={title}"
        lines.append(f"::{_GITHUB_LEVEL[f['level']]} {props}::{_escape_data(text)}")
    return "\n".join(lines)


def sarif(result: CheckResult, version: str) -> str:
    """A SARIF 2.1.0 log with one run: sverify's rules and one result per finding."""
    found = findings(result)
    codes = sorted({f["code"] for f in found})
    rules = [
        {
            "id": code,
            "name": code,
            "shortDescription": {"text": code.replace("_", " ")},
            "fullDescription": {"text": _explain.explain(code) or code},
            "helpUri": f"{INFO_URI}/blob/main/docs/guide.md#the-command-line",
            "defaultConfiguration": {"level": _explain.level_of(code)},
        }
        for code in codes
    ]
    results = []
    for f in found:
        r: dict[str, Any] = {
            "ruleId": f["code"],
            "ruleIndex": codes.index(f["code"]),
            "level": f["level"],
            "message": {"text": f["message"]},
            "locations": [{"physicalLocation": {"artifactLocation": {"uri": f["file"]}}}],
            "properties": {"item": f["item"]},
        }
        if "counterexample" in f:
            r["properties"]["counterexample"] = f["counterexample"]
        results.append(r)
    driver = {"name": "sverify-dbt", "version": version, "informationUri": INFO_URI, "rules": rules}
    log = {
        "$schema": SARIF_SCHEMA,
        "version": "2.1.0",
        "runs": [{"tool": {"driver": driver}, "results": results}],
    }
    return json.dumps(log, indent=2)


def junit(result: CheckResult) -> str:
    """JUnit XML: a suite per model, a case per test or constraint; a test
    that is not proved fails, one not checked is skipped."""
    suites = []
    for m in result.models:
        cases = []
        for t in m.tests + m.constraints:
            name = quoteattr(t.label)
            cls = quoteattr(m.name)
            if t.status == "proved":
                cases.append(f"<testcase classname={cls} name={name}/>")
            elif t.status == "not proved":
                body = escape(
                    _text(t) + (f"\ncounterexample: {t.counterexample}" if t.counterexample else "")
                )
                msg = quoteattr(t.why or t.status)
                cases.append(
                    f"<testcase classname={cls} name={name}>"
                    f"<failure message={msg}>{body}</failure></testcase>"
                )
            else:
                msg = quoteattr(t.why or t.status)
                cases.append(
                    f"<testcase classname={cls} name={name}><skipped message={msg}/></testcase>"
                )
        for issue in m.contract or []:
            name = quoteattr(f"contract {issue.column}")
            cases.append(
                f"<testcase classname={quoteattr(m.name)} name={name}>"
                f"<failure message={quoteattr(issue.problem)}/></testcase>"
            )
        if m.refused:
            cases.append(
                f'<testcase classname={quoteattr(m.name)} name="read">'
                f"<skipped message={quoteattr(m.refused)}/></testcase>"
            )
        failures = sum(c.count("<failure") for c in cases)
        skipped = sum(c.count("<skipped") for c in cases)
        suites.append(
            f'<testsuite name={quoteattr(m.name)} tests="{len(cases)}" '
            f'failures="{failures}" skipped="{skipped}">' + "".join(cases) + "</testsuite>"
        )
    return (
        '<?xml version="1.0" encoding="UTF-8"?>\n<testsuites>' + "".join(suites) + "</testsuites>"
    )

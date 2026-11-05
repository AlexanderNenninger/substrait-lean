"""`check`'s output for CI systems (#793): GitHub's workflow commands
(annotations on a pull request's lines), SARIF 2.1.0 (code scanning) and
JUnit XML (test reports). Each is a view of the same findings."""

from __future__ import annotations

import json
import xml.etree.ElementTree as ET
from typing import Any

from sverify.cli import _explain

SARIF_SCHEMA = "https://json.schemastore.org/sarif-2.1.0.json"
INFO_URI = "https://github.com/AlexanderNenninger/substrait-lean"
_GITHUB_LEVEL = {"error": "error", "warning": "warning", "note": "notice"}


def _escape_data(s: str) -> str:
    return s.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


def _escape_property(s: str) -> str:
    return _escape_data(s).replace(":", "%3A").replace(",", "%2C")


def _title(f: dict[str, Any]) -> str:
    return f"sverify {f['code']}: {f['item']}"


def github(file: str, findings: list[dict[str, Any]], error: dict | None) -> str:
    """One workflow command per finding: `::error file=…,line=…,title=…::…`."""
    lines = []
    for f in findings:
        props = [f"file={_escape_property(file)}"]
        if f.get("line"):
            props.append(f"line={f['line']}")
        props.append(f"title={_escape_property(_title(f))}")
        text = f["message"] + (
            f"\ncounterexample: {f['counterexample']}" if "counterexample" in f else ""
        )
        lines.append(f"::{_GITHUB_LEVEL[f['level']]} {','.join(props)}::{_escape_data(text)}")
    if error is not None:
        title = _escape_property(f"sverify {error['code']}")
        lines.append(
            f"::error file={_escape_property(file)},title={title}::{_escape_data(error['message'])}"
        )
    return "\n".join(lines)


def sarif(file: str, version: str, findings: list[dict[str, Any]], error: dict | None) -> str:
    """A SARIF 2.1.0 log with one run: sverify's rules (its codes, with
    `explain`'s text) and one result per finding."""
    results = list(findings)
    if error is not None:
        results.append(
            {"code": error["code"], "level": "error", "message": error["message"], "item": None}
        )
    codes = sorted({r["code"] for r in results})
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
    index = {code: i for i, code in enumerate(codes)}
    out = []
    for r in results:
        loc: dict[str, Any] = {"artifactLocation": {"uri": file}}
        if r.get("line"):
            loc["region"] = {"startLine": r["line"]}
        props = {
            k: r[k]
            for k in ("item", "nodes", "condition", "counterexample", "hint", "table")
            if r.get(k)
        }
        result: dict[str, Any] = {
            "ruleId": r["code"],
            "ruleIndex": index[r["code"]],
            "level": r["level"],
            "message": {"text": r["message"]},
            "locations": [{"physicalLocation": loc}],
        }
        if props:
            result["properties"] = props
        out.append(result)
    log = {
        "$schema": SARIF_SCHEMA,
        "version": "2.1.0",
        "runs": [
            {
                "tool": {
                    "driver": {
                        "name": "sverify",
                        "version": version,
                        "informationUri": INFO_URI,
                        "rules": rules,
                    }
                },
                "results": out,
            }
        ],
    }
    return json.dumps(log, indent=2)


def junit(
    file: str,
    items: list[tuple[str, list[str], list[dict[str, Any]]]],
    unchecked: list[dict[str, Any]],
    error: dict | None,
) -> str:
    """JUnit XML: one test suite per file, one test case per postcondition
    proved (passing) and per finding (failing); an import error is an
    errored test case."""
    suite = ET.Element("testsuite", name=file)
    tests = failures = errors = skipped = 0
    for name, passed, found in items:
        for label in passed:
            ET.SubElement(suite, "testcase", classname=f"{file}::{name}", name=f"ensures {label}")
            tests += 1
        for f in found:
            case = ET.SubElement(
                suite, "testcase", classname=f"{file}::{name}", name=f.get("condition") or f["code"]
            )
            text = f["message"] + (
                f"\ncounterexample: {f['counterexample']}" if "counterexample" in f else ""
            )
            ET.SubElement(case, "failure", message=f["message"], type=f["code"]).text = text
            tests += 1
            failures += 1
    for f in unchecked:
        case = ET.SubElement(suite, "testcase", classname=f"{file}::{f['item']}", name="unchecked")
        ET.SubElement(case, "skipped", message=f["message"])
        tests += 1
        skipped += 1
    if error is not None:
        case = ET.SubElement(suite, "testcase", classname=file, name=error["code"])
        ET.SubElement(
            case, "error", message=error["message"], type=error.get("type", error["code"])
        )
        tests += 1
        errors += 1
    suite.set("tests", str(tests))
    suite.set("failures", str(failures))
    suite.set("errors", str(errors))
    suite.set("skipped", str(skipped))
    root = ET.Element("testsuites", name="sverify")
    root.append(suite)
    for k in ("tests", "failures", "errors", "skipped"):
        root.set(k, suite.get(k) or "0")
    ET.indent(root)
    return '<?xml version="1.0" encoding="UTF-8"?>\n' + ET.tostring(root, encoding="unicode")

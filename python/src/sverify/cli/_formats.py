"""`check`'s output for CI systems (#793): GitHub's workflow commands
(annotations on a pull request's lines) and SARIF 2.1.0 (code scanning).
Each is a view of the same findings."""

from __future__ import annotations

import json
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

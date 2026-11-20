"""Validate every plan `to_substrait` exports with Substrait's own validator (#862).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

`substrait-validator` (`substrait-io/substrait-validator`, Apache-2.0) checks
that a plan is well formed: its relations, types, extension anchors and
function references, against the Substrait version it was built for. It is
an oracle sverify did not write for what `Report.to_substrait` claims, that
its plans are valid Substrait.

The plans are the coverage cases' (`sverify_dev.coverage_cases`) and the
catalogue's queries (`catalogue/queries/*.toml`, with their contracts), each
verified with `on_inferred="warn"` and exported as bytes once per `shims`
mode that changes the plan (`"apply"` and `"annotate"`; `"refuse"` exports
`"apply"`'s plan or nothing). Each export is

* `agree`: the validator finds no error;
* `refused`: `to_substrait` refuses it (a function outside the YAMLs, a
  spec gap no shim writes); the reason is counted;
* `skipped`: sverify does not prove the plan (its export is refused, or it
  does not verify), so there is nothing to validate;
* `disagree`: the validator reports an error. Each error is a finding,
  keyed by the validator's code and its message with the plan's own names
  and numbers taken out, and the ledger names its record: the `ST-n` entry
  of `upstream/bugs/` (the validator's or the spec's), or the issue of a fix
  to sverify's writer.

The validator pins the protobuf bindings of its own Substrait version
(`substrait-protobuf==0.88.1` at `COMMIT`), which cannot share a process
with sverify's (0.106.0): it runs in its own interpreter, `--python` (or
`$SUBSTRAIT_VALIDATOR_PYTHON`), on the exported files. No release implements
the version sverify writes (`SUBSTRAIT_VERSION`): 0.1.4, the latest on PyPI,
targets Substrait 0.57.1 and knows no extension URNs, so CI builds the
validator at `COMMIT` (the `substrait-validator` job).

`python -m sverify_dev.substrait_validator` prints the totals and the
findings; `--write` rewrites the ledger (`python/tests/substrait_validator.json`),
keeping each finding's record; `--check` fails on a finding the ledger does
not list, a finding with no record and a plan that validated and no longer
does; other changes (main's cases and catalogue move on) only print.
Gates report and never block: CI turns the failure into a warning.
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import subprocess
import sys
import tempfile
import warnings
from collections.abc import Callable, Iterator
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[3]
LEDGER = ROOT / "python" / "tests" / "substrait_validator.json"
#: The validator's commit: `main` after "feat: target Substrait 0.88.1" (#567).
COMMIT = "157c13913ac2e95786d86e75558d4967eabff662"
REPO = "https://github.com/substrait-io/substrait-validator"
#: The `shims` modes whose plans differ (`"refuse"` writes `"apply"`'s or none).
MODES = ("apply", "annotate")

#: Run in the validator's interpreter, with no sverify on its path: read each
#: `*.bin` of the directory and print one JSON line per plan with its errors.
#: The diagnostics are read from the validator's own text: its parse tree as
#: protobuf is deeper than Python's protobuf reads (a `DecodeError`).
WORKER = r"""
import json, re, sys, pathlib
import substrait_validator as v
cfg = v.Config()
line = re.compile(r"^Error at (.*?): (.*) \(code (\d+)\)$")
print(json.dumps({"validator": v.version(), "substrait": v.substrait_version()}))
for p in sorted(pathlib.Path(sys.argv[1]).glob("*.bin")):
    text = v.plan_to_diagnostics_str(p.read_bytes(), cfg)
    errors = [{"path": m[1], "msg": m[2], "code": int(m[3])}
              for m in map(line.match, text.splitlines()) if m]
    print(json.dumps({"plan": p.stem, "errors": errors}))
"""


# -- the plans --------------------------------------------------------------


def plans() -> Iterator[tuple[str, Callable[[], Any]]]:
    """Each plan's id and a function that verifies it into a `Report`."""
    import sverify as sv
    from sverify_dev import catalogue
    from sverify_dev.coverage_cases import CASES

    seen: collections.Counter[str] = collections.Counter()
    for c in CASES:
        key = f"coverage/{c.area}/{c.label}"
        seen[key] += 1
        if seen[key] > 1:
            key += f" #{seen[key]}"
        yield key, (lambda c=c: sv.verify(c.build(), on_inferred="warn"))
    schemas = catalogue.load_schemas()
    for q in catalogue.load_queries():
        if q.not_expressible is not None:
            continue

        def run(q: Any = q) -> Any:
            query = catalogue.build(q, schemas, "native")
            requires, ensures = (
                catalogue.contract(q, schemas, "native") if q.requires is not None else ({}, [])
            )
            tables = (
                catalogue.tables(schemas, q.dataset, "native") if isinstance(query, str) else None
            )
            return sv.verify(
                query, requires=requires, ensures=ensures, tables=tables, on_inferred="warn"
            )

        yield f"catalogue/{q.id}", run


def _first_line(e: BaseException) -> str:
    return (str(e).strip().splitlines() or [type(e).__name__])[0]


#: Plan-specific parts of a refusal or a diagnostic: quoted names, numbers.
_SPECIFIC = [
    (re.compile(r"`[^`]*`"), "`…`"),
    (re.compile(r"'[^']*'"), "'…'"),
    (re.compile(r"\"[^\"]*\""), '"…"'),
    (re.compile(r"\(_\..*\)"), "(…)"),
    (re.compile(r"\b\d+\b"), "N"),
]


def normalize(text: str, limit: int = 160) -> str:
    """`text` without the plan's own names and numbers, so that one cause
    across plans is one key."""
    for pat, rep in _SPECIFIC:
        text = pat.sub(rep, text)
    return text[:limit]


def export(dest: Path, only: str | None = None) -> dict[str, dict[str, Any]]:
    """Verify and export each plan into `dest` (`<n>.bin`); the outcome of
    each refused export, and the file of each written one."""
    from sverify.errors import ExportError

    out: dict[str, dict[str, Any]] = {}
    for n, (key, make) in enumerate(plans()):
        if only and only not in key:
            continue
        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                report = make()
        except Exception as e:  # noqa: BLE001 - a plan sverify does not read
            out[key] = {"outcome": "skipped", "reason": normalize(_first_line(e))}
            continue
        for mode in MODES:
            try:
                data = report.to_substrait("binary", shims=mode)
            except ExportError as e:
                # A plan not proved exports nothing: it is skipped, as one
                # that does not verify is.
                outcome = "skipped" if str(e).startswith("not verified") else "refused"
                out[f"{key} [{mode}]"] = {"outcome": outcome, "reason": normalize(_first_line(e))}
                continue
            name = f"{n:04d}-{mode}"
            (dest / f"{name}.bin").write_bytes(data)
            out[f"{key} [{mode}]"] = {"file": name}
    return out


def python() -> str:
    """The validator's interpreter."""
    found = os.environ.get("SUBSTRAIT_VALIDATOR_PYTHON")
    if not found:
        raise SystemExit(
            "set SUBSTRAIT_VALIDATOR_PYTHON (or --python) to an interpreter with "
            f"substrait-validator at {COMMIT[:8]} ({REPO}); CI's substrait-validator job builds it"
        )
    return found


def validate(src: Path, interpreter: str) -> tuple[dict[str, str], dict[str, list[dict]]]:
    """The validator's version line and each file's errors."""
    proc = subprocess.run(
        [interpreter, "-I", "-c", WORKER, str(src)],
        capture_output=True,
        text=True,
        check=True,
    )
    lines = [json.loads(line) for line in proc.stdout.splitlines() if line.strip()]
    return lines[0], {d["plan"]: d["errors"] for d in lines[1:]}


def finding(error: dict) -> str:
    """The key of a validator error: its code and its message, normalized."""
    return f"{error['code']:04d} {normalize(error['msg'])}"


def ledger(interpreter: str, only: str | None = None) -> dict[str, Any]:
    """A fresh ledger, with the records of the current one's findings."""
    old = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}
    records = {k: v.get("record") for k, v in old.get("findings", {}).items()}
    with tempfile.TemporaryDirectory() as tmp:
        results = export(Path(tmp), only)
        version, errors = validate(Path(tmp), interpreter)
    findings: dict[str, dict[str, Any]] = {}
    for r in results.values():
        if "file" not in r:
            continue
        found = sorted({finding(e) for e in errors.get(r.pop("file"), [])})
        if not found:
            r["outcome"] = "agree"
            continue
        r["outcome"], r["findings"] = "disagree", found
        for f in found:
            entry = findings.setdefault(f, {"plans": 0, "record": records.get(f)})
            entry["plans"] += 1
    counts = collections.Counter(r["outcome"] for r in results.values())
    refusals = collections.Counter(
        r["reason"] for r in results.values() if r["outcome"] == "refused"
    )
    return {
        "validator": {"repo": REPO, "commit": COMMIT, "license": "Apache-2.0", **version},
        "sverify_substrait": _sverify_substrait(),
        "summary": dict(sorted(counts.items())),
        "refusals": dict(refusals.most_common()),
        "findings": dict(sorted(findings.items())),
        "results": dict(sorted(results.items())),
    }


def _sverify_substrait() -> str:
    from sverify.substrait_export import SUBSTRAIT_VERSION

    return ".".join(map(str, SUBSTRAIT_VERSION))


def problems(fresh: dict[str, Any], stored: dict[str, Any]) -> tuple[list[str], list[str]]:
    """How a fresh run differs from the stored ledger: what fails the gate
    (a finding the ledger does not list, one with no record, a plan that
    validated and no longer does), and what only drifted (main's coverage
    cases and catalogue move on: plans added, refusals changed, findings
    gone), which the ledger takes when it is next written."""
    fails, notes = [], []
    known = stored.get("findings", {})
    for f, e in fresh["findings"].items():
        if f not in known:
            fails.append(f"new finding: {f} ({e['plans']} plan(s))")
        elif not e["record"]:
            fails.append(f"finding without a record (ST-n or an issue): {f}")
    notes += [f"finding gone: {f}" for f in known if f not in fresh["findings"]]
    old = stored.get("results", {})
    for key in sorted(fresh["results"].keys() | old.keys()):
        was = old.get(key, {}).get("outcome")
        now = fresh["results"].get(key, {}).get("outcome")
        if was == now:
            continue
        if was == "agree" and now == "disagree":
            fails.append(f"{key}: validated, now {now}")
        else:
            notes.append(f"{key}: {was} -> {now}")
    return fails, notes


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--python", help="the validator's interpreter")
    ap.add_argument("--write", action="store_true", help="rewrite the ledger")
    ap.add_argument("--check", action="store_true", help="compare with the ledger")
    ap.add_argument("--only", help="plans whose id contains this")
    args = ap.parse_args(argv)
    fresh = ledger(args.python or python(), args.only)
    print(json.dumps(fresh["summary"]))
    for f, e in fresh["findings"].items():
        print(f"{e['plans']:4d}  {e['record'] or '(no record)'}  {f}")
    if args.write:
        LEDGER.write_text(json.dumps(fresh, indent=2, ensure_ascii=False) + "\n")
    if args.check:
        fails, notes = problems(fresh, json.loads(LEDGER.read_text()))
        if notes:
            print(f"{len(notes)} change(s) the ledger takes when rewritten:")
            print("\n".join(f"  {n}" for n in notes[:20]))
        if fails:
            print("\n".join(fails), file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

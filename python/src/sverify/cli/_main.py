"""The `sverify` command (#744): argument parsing, the commands and their
output."""

from __future__ import annotations

import argparse
import contextlib
import difflib
import json
import shutil
import subprocess
import sys
from collections.abc import Callable, Sequence
from pathlib import Path
from typing import Any, NoReturn

from sverify.cli import _contract, _explain, _findings, _formats, _text
from sverify.cli._discover import Checked, Discovery, load
from sverify.cli._limits import (
    Budget,
    BudgetExceeded,
    is_out_of_memory,
    memory_limit_from,
    timeout_from,
)
from sverify.cli._suggest import place

#: The exit codes (API review I1).
OK, NOT_PROVED, USAGE, UNSUPPORTED, BUDGET, QUARANTINED, ERROR = 0, 1, 2, 3, 4, 5, 6
EXIT_CODES = """\
exit codes:
  0  proved; a refresh committed every row
  1  not proved
  2  usage error: a flag, a missing file, a node the file lacks
  3  unsupported or refused: a construct outside sverify's model, or no route
  4  time or memory budget exceeded
  5  a refresh committed with rows quarantined, or held a node
  6  error: the file raised, I/O, a crash"""
STATUS = {
    OK: "proved",
    NOT_PROVED: "not_proved",
    USAGE: "usage",
    UNSUPPORTED: "unsupported",
    BUDGET: "budget_exceeded",
    QUARANTINED: "quarantined",
    ERROR: "error",
}
#: The version of the JSON document every command prints (`schemas/cli.schema.json`).
FORMAT = 1
FORMATS = ("text", "json", "github", "sarif", "junit")


class UsageError(Exception):
    """The command line asks for something that is not there."""


def _version() -> str:
    import sverify

    return sverify.__version__


def split_target(target: str) -> tuple[Path, str | None]:
    """`file.py:node` as the file and the node; `file.py` as the file and
    None. A Windows drive's colon is part of the path."""
    head, sep, tail = target.rpartition(":")
    if sep and tail and "/" not in tail and "\\" not in tail and head:
        return Path(head), tail
    return Path(target), None


# What the commands report.


def _item(c: Checked) -> dict[str, Any]:
    r = c.report
    return {
        "name": c.name,
        "nodes": c.nodes,
        "status": c.status,
        "summary": _text.summary(r, c.params) if r is not None else None,
        "links": c.links,
        "report": json.loads(r.to_json()) if r is not None else None,
    }


def _error(code: str, e: BaseException | str, kind: str | None = None) -> dict[str, Any]:
    message = e if isinstance(e, str) else str(e)
    return {
        "code": code,
        "type": kind or (type(e).__name__ if not isinstance(e, str) else "Error"),
        "message": message,
    }


def _classify(e: BaseException) -> tuple[int, str]:
    """The exit code and the error's code for an exception."""
    from sverify.errors import (
        AuditError,
        PostconditionError,
        PreconditionError,
        UnsupportedError,
        VerificationError,
    )

    if isinstance(e, BudgetExceeded):
        return BUDGET, "memory" if e.what == "memory" else "timeout"
    if is_out_of_memory(e):
        return BUDGET, "memory"
    if isinstance(e, UsageError | FileNotFoundError):
        return USAGE, "usage"
    if isinstance(e, UnsupportedError):
        return UNSUPPORTED, "unsupported"
    if isinstance(e, VerificationError | PreconditionError | PostconditionError | AuditError):
        return NOT_PROVED, "not_proved"
    return ERROR, "error"


class Check:
    """A check of a file: what `check` prints in every format."""

    def __init__(self, d: Discovery, target: str | None, budget: Budget):
        self.d, self.target, self.budget = d, target, budget
        self.checked = d.checked if target is None else d.select(target)
        unchecked = d.unchecked if target is None else [t for t in d.unchecked if t == target]
        self.unchecked = unchecked
        self.error: dict[str, Any] | None = None
        if d.error is not None:
            self.code, kind = _classify(d.error)
            self.error = _error(kind, d.error)
        elif target is not None and not self.checked and not unchecked:
            found = sorted({*d.nodes, *(c.name for c in d.checked), *d.unchecked})
            text = f"{d.path} has no node or transform {target!r}"
            self.error = _error(
                "usage", text + (f"; it has {', '.join(found)}" if found else ""), "UsageError"
            )
            self.code = USAGE
        elif not self.checked and not unchecked:
            text = f"{d.path} defines no contracted transform (@sverify.transform)"
            self.error = _error("usage", text, "UsageError")
            self.code = USAGE
        elif any(c.status == "unfinished" for c in self.checked):
            self.code = BUDGET
        elif unchecked or any(c.status == "not_proved" for c in self.checked):
            self.code = NOT_PROVED
        else:
            self.code = OK
        if budget.exceeded and self.code != BUDGET:
            self.code = BUDGET
            self.error = self.error or _error(
                "timeout", f"time budget exceeded ({budget.seconds:g} s)", "BudgetExceeded"
            )

    @property
    def file(self) -> str:
        return str(self.d.path)

    def findings(self) -> list[dict[str, Any]]:
        out = [f for c in self.checked for f in _findings.of(c)]
        return out + [_findings.unchecked(t, self.d) for t in self.unchecked]

    def document(self) -> dict[str, Any]:
        return {
            "file": self.file,
            "target": self.target,
            "items": [_item(c) for c in self.checked],
            "findings": self.findings(),
            "unchecked": self.unchecked,
            "error": self.error,
            "budget": {"timeout": self.budget.seconds, "elapsed": round(self.budget.elapsed, 3)},
        }

    def text(self, full: bool = False) -> str:
        lines: list[str] = []
        where = self.file + (f":{self.target}" if self.target else "")
        findings = self.findings()
        guarantees: dict[str, list[str]] = {}
        checks: dict[str, list[str]] = {}
        for c in self.checked:
            if c.report is None:
                continue
            s = _text.summary(c.report, c.params)
            if s["guarantees"]:
                guarantees[_label(c.name, c.nodes)] = s["guarantees"]
            if s["checks"]:
                checks[_label(c.name, c.nodes)] = s["checks"]
        if self.checked:
            lines.append(f"Contract of {where}")
            if guarantees:
                lines.append("  The output guarantees:")
                lines += [f"    {k}: {'; '.join(v)}" for k, v in guarantees.items()]
            if checks:
                lines.append("  Each refresh checks on the data:")
                lines += [f"    {k}: {'; '.join(v)}" for k, v in checks.items()]
            shown = [f for f in findings if f["code"] != "unchecked"]
            if shown:
                lines.append("  Not proved:")
                for f in shown:
                    lines.append(
                        f"    {_label(f['item'], f['nodes'])}: {f['message']}  [{f['code']}]"
                    )
                    if "counterexample" in f:
                        lines.append(f"      counterexample: {f['counterexample']}")
            lines.append("")
        for c in self.checked:
            r = c.report
            verdict = r.verdict if r is not None else "unfinished: the time budget ran out"
            lines.append(f"{_label(c.name, c.nodes)}: {verdict}")
            if full and r is not None:
                lines += [f"  {line}" for line in str(r).splitlines()[1:]]
                lines += [f"  composition: {m}" for m in c.links]
        lines += [
            f"{t}: not checked, the file never applies it  [unchecked]" for t in self.unchecked
        ]
        if self.error is not None:
            lines.append(f"{self.error['code']}: {self.error['message']}  [{self.error['code']}]")
        codes = sorted(
            {f["code"] for f in findings} | ({self.error["code"]} if self.error else set())
        )
        if codes:
            more = (
                ""
                if full
                else f"; `sverify check --full {self.file}:<node>` prints a node's report"
            )
            lines.append(
                f"`sverify explain <code>` says what a [code] means ({', '.join(codes)}){more}."
            )
        lines.append(STATUS[self.code].replace("_", " "))
        return "\n".join(lines)

    def render(self, fmt: str, full: bool) -> str:
        error = self.error
        if fmt == "github":
            return _formats.github(self.file, self.findings(), error)
        if fmt == "sarif":
            return _formats.sarif(self.file, _version(), self.findings(), error)
        if fmt == "junit":
            items = [(c.name, _findings.passed(c), _findings.of(c)) for c in self.checked]
            unchecked = [_findings.unchecked(t, self.d) for t in self.unchecked]
            return _formats.junit(self.file, items, unchecked, error)
        return self.text(full)


def _label(name: str, nodes: list[str]) -> str:
    return name + (f" ({', '.join(nodes)})" if nodes and nodes != [name] else "")


def _emit(args: argparse.Namespace, code: int, result: dict, text: Callable[[], str]) -> int:
    """Print the outcome in `args.format`, and return the exit code."""
    if args.format == "json":
        doc = {
            "format": FORMAT,
            "sverify": _version(),
            "command": args.command,
            "exit": code,
            "status": result.pop("status", STATUS[code]),
            **result,
        }
        print(json.dumps(doc, indent=2, default=str))
    else:
        out = text()
        if out:
            print(out)
    return code


# Commands.


def _load(path: Path, budget: Budget, d: Discovery) -> Discovery:
    try:
        with budget.armed():
            load(path, d)
    except BudgetExceeded as e:
        d.error = e
    return d


def _on_hard_stop(args: argparse.Namespace, d: Discovery, target: str | None, budget: Budget):
    """What the watchdog prints when the main thread does not stop."""

    def emit() -> None:
        d.error = BudgetExceeded("time", f"{budget.seconds:g} s")
        with contextlib.suppress(Exception):  # print what there is
            d._finish()
        _show(args, Check(d, target, budget))

    return emit


def _show(
    args: argparse.Namespace, check: Check, extra: dict | None = None, text: str | None = None
) -> int:
    if args.format in ("text", "json"):
        result = {**check.document(), **(extra or {})}
        return _emit(args, check.code, result, lambda: text or check.render("text", args.full))
    print(check.render(args.format, args.full))
    return check.code


def _check_file(
    args: argparse.Namespace, path: Path, target: str | None
) -> tuple[Discovery, Check]:
    budget = Budget(timeout_from(args.timeout), lambda: None)
    d = Discovery(path)
    budget.on_hard_stop = _on_hard_stop(args, d, target, budget)
    if not path.is_file():
        raise UsageError(f"{path}: no such file")
    _load(path, budget, d)
    return d, Check(d, target, budget)


def cmd_check(args: argparse.Namespace) -> int:
    path, target = split_target(args.target)
    if path.is_dir() or path.name == "dbt_project.yml":
        return _dbt(args, path)
    d, check = _check_file(args, path, target)
    if not (args.fix or args.diff):
        return _show(args, check)
    plan = place(path, check.checked)
    before = path.read_text()
    diff = ""
    if plan.text is not None:
        diff = "".join(
            difflib.unified_diff(
                before.splitlines(keepends=True),
                plan.text.splitlines(keepends=True),
                f"a/{path}".replace("//", "/"),
                f"b/{path}".replace("//", "/"),
            )
        )
    applied = bool(args.fix and plan.text is not None)
    if applied:
        assert plan.text is not None
        path.write_text(plan.text)
        _, check = _check_file(args, path, target)
    extra = {
        "fixes": [
            {
                "transform": f.transform,
                "requires": f.conditions,
                "placed": f.placed,
                "reason": f.reason,
            }
            for f in plan.fixes
        ],
        "diff": diff,
        "applied": applied,
    }
    lines = []
    if not plan.fixes:
        lines.append("No preconditions to add: no proof in the file needs one.")
    for f in plan.fixes:
        lines += [f"{f.transform}: requires {p}: {', '.join(cs)}" for p, cs in f.conditions.items()]
        if f.reason:
            lines.append(f"  not placed: {f.reason}")
    if diff:
        lines.append(diff.rstrip("\n"))
    if applied:
        lines += [f"wrote {path}; checked again:", check.text(args.full)]
    elif diff:
        lines.append("`sverify check --fix` writes this.")
    else:
        lines.append(check.text(args.full))
    return _show(args, check, extra, "\n".join(lines))


def _dbt(args: argparse.Namespace, path: Path) -> int:
    """A dbt project: `sverify-dbt check`, its exit status passed through."""
    exe = shutil.which("sverify-dbt")
    if exe is None:
        message = "a dbt project: install sverify-dbt to check it (pip install sverify-dbt)"
        result = {"file": str(path), "error": _error("usage", message, "UsageError")}
        return _emit(args, USAGE, result, lambda: message)
    project = path if path.is_dir() else path.parent
    flags = [] if args.format == "text" else ["--format", args.format]
    return subprocess.call([exe, "check", str(project), *flags])


def _outcome_code(outcome: str) -> int:
    return QUARANTINED if outcome in ("quarantined", "held") else OK


def cmd_refresh(args: argparse.Namespace) -> int:
    from sverify._hooks import planned
    from sverify.errors import RouteError

    if args.format not in ("text", "json"):
        raise UsageError(f"refresh prints text or json, not {args.format}")
    path, target = split_target(args.target)
    if target is None:
        raise UsageError("refresh takes <file>:<node>")
    if not path.is_file():
        raise UsageError(f"{path}: no such file")
    budget = Budget(timeout_from(args.timeout), lambda: None)
    d = Discovery(path)
    budget.on_hard_stop = _on_hard_stop(args, d, target, budget)
    result: dict[str, Any] = {"file": str(path), "target": target, "nodes": [], "error": None}
    try:
        with planned(budget.disarm), budget.armed():
            load(path, d)
            if d.error is not None:
                raise d.error
            node = d.nodes.get(target)
            if node is None:
                have = ", ".join(sorted(d.nodes)) or "none"
                raise UsageError(f"{path} has no node {target!r}; it has {have}")
            # Proofs and planning end where `Group.refresh` has chosen its
            # routes (`sverify._hooks.planned`): the data moves unbounded.
            done = node.refresh(engine=args.engine, audit=args.audit, lineage=args.lineage)
    except BaseException as e:  # noqa: BLE001 - every outcome has an exit code
        if isinstance(e, KeyboardInterrupt | SystemExit):
            raise
        code, kind = _classify(e)
        if isinstance(e, RouteError):
            # Not proved, or proved with no route to the engine (refused).
            unproved = any(c.status == "not_proved" for c in d.select(target))
            code, kind = (NOT_PROVED, "not_proved") if unproved else (UNSUPPORTED, "refused")
        result["error"] = _error(kind, e)
        result["items"] = [_item(c) for c in d.select(target)]
        message = f"{kind}: {e}  [{kind}]"
        return _emit(args, code, result, lambda: message)
    for s in done.nodes:
        w = s.write
        result["nodes"].append(
            {
                "node": s.node,
                "summary": s.summary(),
                "started": s.started,
                "outcome": s.outcome,
                "held": s.held,
                "quarantined": s.quarantined,
                "quarantine_table": s.quarantine_table,
                "quarantine": [q.to_dict() for q in s.quarantine],
                "route": str(s.route) if s.route is not None else None,
                "write": None
                if w is None
                else {
                    "mode": w.mode,
                    "version": w.version,
                    "inserted": w.inserted,
                    "deleted": w.deleted,
                },
            }
        )
    outcome = done.outcome
    code = _outcome_code(outcome)
    result["outcome"] = outcome
    result["memory_limit"] = args.memory_limit
    if code != OK:
        result["status"] = outcome
    result["alert"] = done.alert()

    def human() -> str:
        alert = done.alert()
        return done.summary() + ("" if alert is None else "\n\n" + alert)

    return _emit(args, code, result, human)


def cmd_explain(args: argparse.Namespace) -> int:
    text = _explain.explain(args.code)
    if text is None:
        known = ", ".join(sorted(_explain.CODES))
        raise UsageError(f"{args.code!r} is no code of sverify's; the codes are {known}")
    code = _explain.code_of(args.code)
    result = {"code": code, "level": _explain.level_of(code), "text": text}
    return _emit(args, OK, result, lambda: f"[{code}] {text}")


class _Parser(argparse.ArgumentParser):
    def error(self, message: str) -> NoReturn:
        self.print_usage(sys.stderr)
        self.exit(USAGE, f"{self.prog}: error: {message}\n")


def parser() -> argparse.ArgumentParser:
    common = _Parser(add_help=False)
    common.add_argument(
        "--format",
        "--output-format",
        dest="format",
        choices=FORMATS,
        default="text",
        help="text (the default), json, or for check: github (annotations), sarif, junit",
    )
    common.add_argument(
        "--json", dest="format", action="store_const", const="json", help="--format json"
    )
    common.add_argument(
        "--timeout",
        type=float,
        default=None,
        help="seconds for proof, planning and checking, never for moving data "
        "(default: $SVERIFY_TIMEOUT or 30; 0 turns it off)",
    )
    common.add_argument(
        "--memory-limit",
        default=None,
        help="DuckDB's memory limit, such as 2GB, past which it spills to disk "
        "(default: $SVERIFY_MEMORY_LIMIT, else DuckDB's own)",
    )
    p = _Parser(
        prog="sverify",
        description="Check, fix and run sverify pipelines.",
        epilog=EXIT_CODES,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument("--version", action="version", version=f"sverify {_version()}")
    sub = p.add_subparsers(dest="command", required=True, parser_class=_Parser)
    c = sub.add_parser(
        "check",
        parents=[common],
        help="prove every transform and node of a file",
        epilog=EXIT_CODES,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    c.add_argument("target", help="file.py, file.py:<node or transform>, or a dbt project")
    c.add_argument("--full", action="store_true", help="print each node's full report")
    fix = c.add_mutually_exclusive_group()
    fix.add_argument(
        "--fix",
        action="store_true",
        help="write the preconditions the proofs need into requires=, then check again",
    )
    fix.add_argument("--diff", action="store_true", help="show what --fix would write")
    c.set_defaults(run=cmd_check)
    r = sub.add_parser(
        "refresh",
        parents=[common],
        help="run a node and report what changed",
        epilog=EXIT_CODES,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    r.add_argument("target", help="file.py:<node>")
    r.add_argument("--engine", default="duckdb", help="duckdb (the default), polars or spark")
    r.add_argument("--audit", action="store_true", help="compare every batch with recomputation")
    r.add_argument(
        "--lineage",
        nargs="?",
        const=True,
        default=None,
        metavar="TARGET",
        help="send OpenLineage run events: to a file (JSON lines), 'console', a URL "
        "(Marquez), or without TARGET as openlineage.yml and OPENLINEAGE_* say",
    )
    r.set_defaults(run=cmd_refresh, full=False)
    e = sub.add_parser("explain", parents=[common], help="what a [code] of check's output means")
    e.add_argument("code", help="a code from check's output, such as may_be_false")
    e.set_defaults(run=cmd_explain, full=False)
    _contract.add_parser(sub)
    return p


def main(argv: Sequence[str] | None = None) -> int:
    """Run the `sverify` command with `argv` (default: `sys.argv[1:]`) and
    return its exit code: 0 proved (a refresh committed every row), 1 not
    proved, 2 usage error, 3 unsupported or refused, 4 time or memory budget
    exceeded, 5 a refresh quarantined rows or held a node, 6 error."""
    try:
        args = parser().parse_args(argv)
    except SystemExit as e:
        return e.code if isinstance(e.code, int) else USAGE
    try:
        memory_limit_from(args.memory_limit)
        return args.run(args)
    except BaseException as e:  # noqa: BLE001 - every outcome has an exit code
        if isinstance(e, KeyboardInterrupt | SystemExit):
            raise
        code, kind = _classify(e)
        message = f"{kind}: {e}"
        if isinstance(e, ValueError) and "memory limit" in str(e):
            code, kind = USAGE, "usage"
        return _emit(args, code, {"error": _error(kind, e)}, lambda: message)

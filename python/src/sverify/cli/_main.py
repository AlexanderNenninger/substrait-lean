"""The `sverify` command (#744): argument parsing, the commands and their
output."""

from __future__ import annotations

import argparse
import contextlib
import difflib
import json
import shutil
import subprocess
from collections.abc import Callable, Sequence
from pathlib import Path
from typing import Any

from sverify.cli import _explain, _text
from sverify.cli._discover import Checked, Discovery, load
from sverify.cli._limits import (
    Budget,
    BudgetExceeded,
    is_out_of_memory,
    memory_limit_from,
    timeout_from,
)
from sverify.cli._suggest import place

PROVED, NOT_PROVED, REFUSED, BUDGET, ERROR, ATTENTION = 0, 1, 2, 3, 4, 5
STATUS = {
    PROVED: "proved",
    NOT_PROVED: "not_proved",
    REFUSED: "refused",
    BUDGET: "budget_exceeded",
    ERROR: "error",
    ATTENTION: "quarantined",
}
#: A refresh that completed, by `Refresh.outcome` (#184): rows quarantined
#: and a node held both need attention, and exit 5; the JSON's `status` says
#: which.
OUTCOME_EXIT = {"ok": PROVED, "quarantined": ATTENTION, "held": ATTENTION}


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


# What each command's output carries.


def _problems(c: Checked) -> list[dict[str, Any]]:
    """The problems of one application, each with its `explain` code."""
    out: list[dict[str, Any]] = []
    r = c.report
    if r is None:
        return [{"code": "timeout", "message": "the time budget ran out while proving it"}]
    for cond in r.ensures:
        if cond.portable or cond.checked:
            continue
        p: dict[str, Any] = {
            "code": _explain.code_of(cond.reason or "unknown"),
            "message": f"ensures {cond.label}: {cond.why}",
            "condition": cond.label,
        }
        if cond.counterexample is not None:
            p["counterexample"] = str(cond.counterexample)
        out.append(p)
    for n in r.needs:
        p = {"code": "needs", "message": f"needs {n.code} on {n.table}", "table": n.table}
        if n.issue is not None:
            p["message"] += f" (else {n.issue.kind} in {n.issue.what})"
        out.append(p)
    for i in r.errors:
        p = {"code": _explain.code_of(i.kind), "message": f"may fail: {i.message}"}
        if i.hint:
            p["hint"] = i.hint
        out.append(p)
    if r.transfer:
        n_opts = len(r.transfer)
        out.append({"code": "transfer", "message": f"Substrait allows more at {n_opts} option(s)"})
    if r.floats_unmet:
        out.append({"code": "floats", "message": r.floats_unmet})
    out += [{"code": "composition", "message": m} for m in c.links]
    return out


def _needs(c: Checked) -> list[dict[str, Any]]:
    if c.report is None:
        return []
    return [
        {
            "table": n.table,
            "parameter": c.params.get(n.table, n.table),
            "column": n.column,
            "op": n.op,
            "value": n.value,
            "sql": n.sql,
            "code": n.code,
        }
        for n in c.report.needs
    ]


def _item(c: Checked) -> dict[str, Any]:
    r = c.report
    return {
        "name": c.name,
        "nodes": c.nodes,
        "status": c.status,
        "verdict": r.verdict if r is not None else "unfinished: the time budget ran out",
        "summary": _text.summary(r, c.params) if r is not None else None,
        "problems": _problems(c),
        "needs": _needs(c),
        "facts": dict(r.facts) if r is not None else {},
    }


def _exception(e: BaseException) -> dict[str, Any]:
    from sverify.errors import UnsupportedError

    if isinstance(e, BudgetExceeded):
        code = "memory" if e.what == "memory" else "timeout"
    elif isinstance(e, UnsupportedError):
        code = "refused"
    elif is_out_of_memory(e):
        code = "memory"
    else:
        code = "error"
    return {"code": code, "type": type(e).__name__, "message": str(e)}


def _exit_for_error(e: BaseException) -> int:
    from sverify.errors import (
        AuditError,
        PostconditionError,
        PreconditionError,
        UnsupportedError,
        VerificationError,
    )

    if isinstance(e, BudgetExceeded) or is_out_of_memory(e):
        return BUDGET
    if isinstance(e, UnsupportedError):
        return REFUSED
    if isinstance(e, VerificationError | PreconditionError | PostconditionError | AuditError):
        return NOT_PROVED
    return ERROR


def _check_result(d: Discovery, target: str | None, budget: Budget) -> tuple[int, dict]:
    checked = d.checked if target is None else d.select(target)
    unchecked = d.unchecked if target is None else [t for t in d.unchecked if t == target]
    result: dict[str, Any] = {
        "file": str(d.path),
        "target": target,
        "items": [_item(c) for c in checked],
        "unchecked": unchecked,
        "error": _exception(d.error) if d.error is not None else None,
    }
    if d.error is not None:
        code = _exit_for_error(d.error)
    elif target is not None and not checked and not unchecked:
        found = sorted({*d.nodes, *(c.name for c in d.checked), *d.unchecked})
        result["error"] = {
            "code": "error",
            "type": "LookupError",
            "message": f"{d.path} has no node or transform {target!r}"
            + (f"; it has {', '.join(found)}" if found else ""),
        }
        code = ERROR
    elif not checked and not unchecked:
        result["error"] = {
            "code": "error",
            "type": "LookupError",
            "message": f"{d.path} defines no contracted transform (@sverify.transform)",
        }
        code = ERROR
    elif any(c.status == "unfinished" for c in checked):
        code = BUDGET
    elif unchecked or any(c.status == "not_proved" for c in checked):
        code = NOT_PROVED
    else:
        code = PROVED
    if budget.exceeded and code != BUDGET:
        code = BUDGET
    return code, result


# Output.


def _emit(
    args: argparse.Namespace, command: str, code: int, result: dict, human: Callable[[], str]
) -> int:
    if args.json:
        doc = {
            "format": "provisional",
            "sverify": _version(),
            "command": command,
            "exit": code,
            "status": result.pop("status", None) or STATUS[code],
            **result,
        }
        print(json.dumps(doc, indent=2, default=str))
    else:
        text = human()
        if text:
            print(text)
    return code


def _human_check(code: int, result: dict) -> str:
    items = result["items"]
    lines: list[str] = []
    where = result["file"] + (f":{result['target']}" if result["target"] else "")
    guarantees = [(i, g) for i in items if i["summary"] for g in i["summary"]["guarantees"]]
    checks = [(i, g) for i in items if i["summary"] for g in i["summary"]["checks"]]
    refused = [(i, p) for i in items for p in i["problems"]]
    if items:
        lines.append(f"Contract of {where}")
        if guarantees:
            lines.append("  The output guarantees:")
            lines += _grouped(guarantees)
        if checks:
            lines.append("  Each refresh checks on the data:")
            lines += _grouped(checks)
        if refused:
            lines.append("  Not proved:")
            for i, p in refused:
                lines.append(f"    {_label(i)}: {p['message']}  [{p['code']}]")
                if "counterexample" in p:
                    lines.append(f"      counterexample: {p['counterexample']}")
        lines.append("")
    for i in items:
        lines.append(f"{_label(i)}: {i['verdict']}")
    lines += [
        f"{t}: not checked, the file never applies it  [unchecked]" for t in result["unchecked"]
    ]
    if err := result.get("error"):
        lines.append(f"{err['code']}: {err['message']}  [{err['code']}]")
    codes = sorted(
        {p["code"] for i in items for p in i["problems"]}
        | ({"unchecked"} if result["unchecked"] else set())
        | ({err["code"]} if err else set())
    )
    if codes:
        lines.append(
            f"`sverify explain <code>` says what each [code] means ({', '.join(codes)}); "
            f"`sverify explain {result['file']}:<node>` prints a node's full report."
        )
    lines.append(STATUS[code].replace("_", " "))
    return "\n".join(lines)


def _grouped(pairs: list[tuple[dict, str]]) -> list[str]:
    """One line per item: its label, then its entries."""
    out: dict[str, list[str]] = {}
    for item, text in pairs:
        out.setdefault(_label(item), []).append(text)
    return [f"    {k}: {'; '.join(v)}" for k, v in out.items()]


def _label(item: dict) -> str:
    nodes = item["nodes"]
    return item["name"] + (f" ({', '.join(nodes)})" if nodes and nodes != [item["name"]] else "")


# Commands.


def _discover(args: argparse.Namespace, path: Path, budget: Budget) -> Discovery:
    d = Discovery(path)
    try:
        with budget.armed():
            load(path, d)
    except BudgetExceeded as e:
        d.error = e
    return d


def _partial(
    args: argparse.Namespace, command: str, d: Discovery, target: str | None, budget: Budget
):
    """What the watchdog prints when the main thread does not stop."""

    def emit() -> None:
        d.error = BudgetExceeded("time", f"{budget.seconds:g} s")
        with contextlib.suppress(Exception):  # print what there is
            d._finish()
        _, result = _check_result(d, target, budget)
        _emit(args, command, BUDGET, result, lambda: _human_check(BUDGET, result))

    return emit


def cmd_check(args: argparse.Namespace) -> int:
    path, target = split_target(args.target)
    if path.is_dir() or path.name == "dbt_project.yml":
        return _dbt(args, path)
    budget = Budget(timeout_from(args.timeout), lambda: None)
    d = Discovery(path)
    budget.on_hard_stop = _partial(args, "check", d, target, budget)
    try:
        with budget.armed():
            load(path, d)
    except BudgetExceeded as e:
        d.error = e
    code, result = _check_result(d, target, budget)
    result["budget"] = {"timeout": budget.seconds, "elapsed": round(budget.elapsed, 3)}
    return _emit(args, "check", code, result, lambda: _human_check(code, result))


def _dbt(args: argparse.Namespace, path: Path) -> int:
    """A dbt project: `sverify-dbt check`, its exit status passed through."""
    exe = shutil.which("sverify-dbt")
    if exe is None:
        result = {
            "file": str(path),
            "error": {
                "code": "error",
                "type": "FileNotFoundError",
                "message": "a dbt project: install sverify-dbt to check it "
                "(pip install sverify-dbt)",
            },
        }
        return _emit(args, "check", ERROR, result, lambda: result["error"]["message"])
    project = path if path.is_dir() else path.parent
    return subprocess.call([exe, "check", str(project), *(["--json"] if args.json else [])])


def cmd_suggest(args: argparse.Namespace) -> int:
    path, target = split_target(args.target)
    budget = Budget(timeout_from(args.timeout), lambda: None)
    d = Discovery(path)
    budget.on_hard_stop = _partial(args, "suggest", d, target, budget)
    try:
        with budget.armed():
            load(path, d)
    except BudgetExceeded as e:
        d.error = e
    checked = d.checked if target is None else d.select(target)
    plan = place(path, checked)
    before = path.read_text()
    diff = (
        "".join(
            difflib.unified_diff(
                before.splitlines(keepends=True),
                plan.text.splitlines(keepends=True),
                f"a/{path}".replace("//", "/"),
                f"b/{path}".replace("//", "/"),
            )
        )
        if plan.text is not None
        else ""
    )
    applied = False
    recheck: tuple[int, dict] | None = None
    if args.apply and plan.text is not None:
        path.write_text(plan.text)
        applied = True
        again = _discover(args, path, Budget(timeout_from(args.timeout), lambda: None))
        recheck = _check_result(again, target, budget)
    code, result = recheck if recheck is not None else _check_result(d, target, budget)
    result["fixes"] = [
        {"transform": f.transform, "requires": f.conditions, "placed": f.placed, "reason": f.reason}
        for f in plan.fixes
    ]
    result["diff"] = diff
    result["applied"] = applied

    def human() -> str:
        lines = []
        if not plan.fixes:
            lines.append("No preconditions to add: no proof in the file needs one.")
        for f in plan.fixes:
            for p, cs in f.conditions.items():
                lines.append(f"{f.transform}: requires {p}: {', '.join(cs)}")
            if f.reason:
                lines.append(f"  not placed: {f.reason}")
        if diff:
            lines.append(diff.rstrip("\n"))
        if applied:
            lines.append(f"wrote {path}; checked again:")
            lines.append(_human_check(code, result))
        elif diff:
            lines.append("`sverify suggest --apply` writes this.")
        return "\n".join(lines)

    return _emit(args, "suggest", code, result, human)


def cmd_refresh(args: argparse.Namespace) -> int:
    from sverify._hooks import planned

    path, target = split_target(args.target)
    if target is None:
        result = {
            "file": str(path),
            "error": {
                "code": "error",
                "type": "ValueError",
                "message": "refresh takes <file>:<node>",
            },
        }
        return _emit(args, "refresh", ERROR, result, lambda: result["error"]["message"])
    budget = Budget(timeout_from(args.timeout), lambda: None)
    d = Discovery(path)
    budget.on_hard_stop = _partial(args, "refresh", d, target, budget)
    result: dict[str, Any] = {"file": str(path), "target": target, "nodes": [], "error": None}
    try:
        with planned(budget.disarm), budget.armed():
            load(path, d)
            if d.error is not None:
                raise d.error
            node = d.nodes.get(target)
            if node is None:
                have = ", ".join(sorted(d.nodes)) or "none"
                raise LookupError(f"{path} has no node {target!r}; it has {have}")
            # Proofs and planning end where `Group.refresh` has chosen its
            # routes (`sverify._hooks.planned`): the data moves unbounded.
            done = node.refresh(engine=args.engine, audit=args.audit)
    except BaseException as e:  # noqa: BLE001 - every outcome has an exit code
        if isinstance(e, KeyboardInterrupt | SystemExit):
            raise
        from sverify.errors import RouteError

        code = _exit_for_error(e)
        result["error"] = _exception(e)
        if isinstance(e, RouteError):
            # Not proved, or proved with no route to the engine (a refusal).
            unproved = any(c.status == "not_proved" for c in d.select(target))
            code = NOT_PROVED if unproved else REFUSED
            result["error"]["code"] = "not-proved" if unproved else "refused"
        if code in (NOT_PROVED, REFUSED):
            result["items"] = [_item(c) for c in d.select(target)]
        return _emit(
            args,
            "refresh",
            code,
            result,
            lambda: f"{result['error']['code']}: {result['error']['message']}",
        )
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
    result["memory_limit"] = args.memory_limit
    result["outcome"] = done.outcome
    result["alert"] = done.alert()

    def human() -> str:
        alert = done.alert()
        return done.summary() + ("" if alert is None else "\n\n" + alert)

    if done.outcome != "ok":
        result["status"] = done.outcome
    return _emit(args, "refresh", OUTCOME_EXIT[done.outcome], result, human)


def cmd_explain(args: argparse.Namespace) -> int:
    text = _explain.explain(args.what)
    if text is not None:
        code = _explain.code_of(args.what)
        return _emit(
            args, "explain", PROVED, {"code": code, "text": text}, lambda: f"[{code}] {text}"
        )
    path, target = split_target(args.what)
    if path.suffix != ".py" and not path.is_file():
        known = ", ".join(sorted(_explain.CODES))
        result = {
            "error": {
                "code": "error",
                "type": "LookupError",
                "message": f"{args.what!r} is no code and no file; the codes are {known}",
            }
        }
        return _emit(args, "explain", ERROR, result, lambda: result["error"]["message"])
    budget = Budget(timeout_from(args.timeout), lambda: None)
    d = _discover(args, path, budget)
    code, result = _check_result(d, target, budget)
    checked = d.checked if target is None else d.select(target)
    for item, c in zip(result["items"], checked, strict=True):
        item["report"] = str(c.report) if c.report is not None else None

    def human() -> str:
        lines = []
        for item in result["items"]:
            lines.append(f"{_label(item)}:")
            lines += [f"  {line}" for line in (item["report"] or item["verdict"]).splitlines()]
            lines += [
                f"  composition: {p['message']}"
                for p in item["problems"]
                if p["code"] == "composition"
            ]
        if err := result.get("error"):
            lines.append(f"{err['code']}: {err['message']}")
        return "\n".join(lines)

    return _emit(args, "explain", code, result, human)


def parser() -> argparse.ArgumentParser:
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--json", action="store_true", help="print a JSON document for tools")
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
    p = argparse.ArgumentParser(
        prog="sverify",
        description="Check, fix and run sverify pipelines. Exit codes: 0 proved, "
        "1 not proved, 2 refused, 3 budget exceeded (time or memory), 4 error.",
    )
    p.add_argument("--version", action="version", version=f"sverify {_version()}")
    sub = p.add_subparsers(dest="command", required=True)
    c = sub.add_parser("check", parents=[common], help="prove every transform and node of a file")
    c.add_argument("target", help="file.py, file.py:<node or transform>, or a dbt project")
    c.set_defaults(run=cmd_check)
    s = sub.add_parser(
        "suggest", parents=[common], help="write the preconditions proofs need into requires="
    )
    s.add_argument("target", help="file.py or file.py:<node or transform>")
    s.add_argument(
        "--apply", action="store_true", help="write the fixes into the file, then check it again"
    )
    s.set_defaults(run=cmd_suggest)
    r = sub.add_parser("refresh", parents=[common], help="run a node and report what changed")
    r.add_argument("target", help="file.py:<node>")
    r.add_argument("--engine", default="duckdb", help="duckdb (default), polars or spark")
    r.add_argument("--audit", action="store_true", help="compare every batch with recomputation")
    r.set_defaults(run=cmd_refresh)
    e = sub.add_parser(
        "explain", parents=[common], help="explain a [code], or print a node's full report"
    )
    e.add_argument("what", help="a code from check's output, or file.py[:<node>]")
    e.set_defaults(run=cmd_explain)
    return p


def main(argv: Sequence[str] | None = None) -> int:
    """Run the `sverify` command with `argv` (default: `sys.argv[1:]`) and
    return its exit code: 0 proved, 1 not proved, 2 refused, 3 budget
    exceeded (time or memory), 4 error; for `refresh`, 5 completed with rows
    quarantined or a node held (#184)."""
    args = parser().parse_args(argv)
    try:
        memory_limit_from(args.memory_limit)
        return args.run(args)
    except BudgetExceeded as e:
        message = str(e)
        return _emit(args, args.command, BUDGET, {"error": _exception(e)}, lambda: message)
    except Exception as e:  # noqa: BLE001 - every outcome has an exit code
        code, message = _exit_for_error(e), f"{type(e).__name__}: {e}"
        return _emit(args, args.command, code, {"error": _exception(e)}, lambda: message)

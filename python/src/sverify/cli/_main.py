"""The `sverify` command (#744): argument parsing, the commands and their
output."""

from __future__ import annotations

import argparse
import contextlib
import difflib
import json
import os
import shutil
import subprocess
import sys
from collections.abc import Callable, Sequence
from pathlib import Path
from typing import Any, NoReturn

from sverify.cli import _contract, _explain, _findings, _formats
from sverify.cli._common import (  # noqa: F401  (re-exported)
    BUDGET,
    ERROR,
    HELD,
    NO_ROUTE,
    NOT_PROVED,
    OK,
    QUARANTINED,
    UNSUPPORTED,
    USAGE,
    UsageError,
    split_target,
)
from sverify.cli._discover import Checked, Discovery, load
from sverify.cli._limits import (
    Budget,
    BudgetExceeded,
    memory_limit_from,
    timeout_from,
)
from sverify.cli._sql import load_sql
from sverify.cli._suggest import place

EXIT_CODES = """\
exit codes:
  0  proved; a refresh committed every row
  1  not proved
  2  usage error: a flag, a missing file, a node the file lacks
  3  unsupported: a construct outside sverify's model
  4  time or memory budget exceeded
  5  a refresh committed with rows quarantined
  6  error: the file raised, I/O, a crash
  7  refused: no route takes the proved node to the engine
  8  a refresh held a node"""
STATUS = {
    OK: "proved",
    NOT_PROVED: "not_proved",
    USAGE: "usage",
    UNSUPPORTED: "unsupported",
    BUDGET: "budget_exceeded",
    QUARANTINED: "quarantined",
    ERROR: "error",
    NO_ROUTE: "refused",
    HELD: "held",
}
#: The version of the JSON document every command prints (`schemas/cli.schema.json`).
#: Format 1, before 1.0, named a write's `inserts` and `deletes` `inserted` and
#: `deleted` (#2345).
FORMAT = 2
FORMATS = ("text", "json", "github", "sarif")


#: What `--fix` and `--diff` say when they have fixes (#881 1.4, ruling 219 D4).
NARROWS = "These preconditions narrow the input each node accepts: its sources must meet them."


def _version() -> str:
    import sverify

    return sverify.__version__


# What the commands report.


def _item(c: Checked) -> dict[str, Any]:
    r = c.report
    return {
        "name": c.name,
        "nodes": c.nodes,
        "status": c.status,
        "relaxations": c.relaxations,
        "summary": r._plain_contract(c.params) if r is not None else None,
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
    try:
        from sverify.errors import (
            AuditError,
            MemoryLimitError,
            PostconditionError,
            PreconditionError,
            UnsupportedError,
            VerificationError,
        )
    except Exception:  # noqa: BLE001 - the import failure is the error being classified (#1585)
        return ERROR, "error"

    if isinstance(e, BudgetExceeded):
        return BUDGET, "memory" if e.what == "memory" else "timeout"
    if isinstance(e, MemoryLimitError):
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

    def __init__(
        self, d: Discovery, target: str | None, budget: Budget, require_proved: bool = False
    ):
        self.d, self.target, self.budget = d, target, budget
        self.require_proved = require_proved
        self.checked = d.checked if target is None else d.select(target)
        unchecked = d.unchecked if target is None else [t for t in d.unchecked if t == target]
        self.unchecked = unchecked
        self.error: dict[str, Any] | None = None
        self._uses: list[tuple[str, Any]] | None = None
        self.drift: dict[str, Any] | None = None
        """With `--against-sink`, per stored node, how its contract compares
        with its sink's last committed one; None for a sink with none."""
        self._drift_findings: list[dict[str, Any]] = []
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
        elif (
            unchecked
            or any(c.status == "not_proved" for c in self.checked)
            or (require_proved and any(c.status == "checked" for c in self.checked))
        ):
            self.code = NOT_PROVED
        else:
            self.code = OK
        if budget.exceeded and self.code != BUDGET:
            self.code = BUDGET
            self.error = self.error or _error(
                "timeout",
                f"time budget exceeded ({budget.seconds:g} s); "
                "raise it with `--timeout` or `SVERIFY_TIMEOUT`",
                "BudgetExceeded",
            )

    @property
    def file(self) -> str:
        return str(self.d.path)

    def credential_uses(self) -> list[tuple[str, Any]]:
        """Per node variable, the credentials its refresh uses, each
        table and credential once."""
        if self._uses is None:
            self._uses = []
            seen: set[Any] = set()
            for var, node in self.d.nodes.items():
                if self.target is not None and var != self.target:
                    continue
                try:
                    got = node.credentials()
                except Exception:  # noqa: BLE001 - a listing never fails a check
                    continue
                for u in got:
                    if u not in seen:
                        seen.add(u)
                        self._uses.append((var, u))
        return self._uses

    def findings(self) -> list[dict[str, Any]]:
        out = [f for c in self.checked for f in _findings.of(c)]
        if self.require_proved:
            out += [_findings.checked_only(c) for c in self.checked if c.status == "checked"]
        out += [_findings.unchecked(t, self.d) for t in self.unchecked]
        return out + _findings.credentials(self.credential_uses()) + self._drift_findings

    def compare_sinks(self) -> None:
        """`--against-sink` (#769, ruling 189): each stored node's contract
        against its sink's last committed one. Reads the record, no data. A
        sink that cannot be read is an error of its own (exit 6)."""
        from sverify.io._common import drift
        from sverify.nodes import _Stored

        self.drift = {}
        for var, node in self.d.nodes.items():
            if (self.target is not None and var != self.target) or not isinstance(node, _Stored):
                continue
            try:
                committed = node.sink.contract()
                got = None if committed is None else drift(committed, node)
            except BudgetExceeded:
                raise
            except Exception as e:  # noqa: BLE001 - never reported as unchanged
                self.code, self.error = ERROR, _error("error", f"{var}'s sink: {e}")
                return
            self.drift[var] = None if got is None else got.to_dict()
            if got is None:
                continue
            self._drift_findings += _findings.drift(var, got)
            if any(got.weakened.values()) and self.code in (OK,):
                self.code = NOT_PROVED

    def document(self) -> dict[str, Any]:
        return {
            "file": self.file,
            "target": self.target,
            "items": [_item(c) for c in self.checked],
            "findings": self.findings(),
            "unchecked": self.unchecked,
            "credentials": [{"node": v, **u.to_dict()} for v, u in self.credential_uses()],
            "error": self.error,
            "budget": {"timeout": self.budget.seconds, "elapsed": round(self.budget.elapsed, 3)},
            **({} if self.drift is None else {"drift": self.drift}),
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
            s = c.report._plain_contract(c.params)
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
            uses = self.credential_uses()
            if uses:
                lines.append("  Credentials, by name:")
                lines += [f"    {u}" for _, u in uses]
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
            verdict = r._summary if r is not None else "unfinished: the time budget ran out"
            lines.append(f"{_label(c.name, c.nodes)}: {verdict}")
            if full and r is not None:
                lines += [f"  {line}" for line in r.details().splitlines()[1:]]
                lines += [f"  composition: {m}" for m in c.links]
        lines += [
            f"{t}: not checked, the file never applies it; declare its input schemas with "
            "@sv.transform(schemas=...)  [unchecked]"
            for t in self.unchecked
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
        if not self.checked:  # a node's line has said it otherwise
            lines.append(STATUS[self.code].replace("_", " "))
        return "\n".join(lines)

    def render(self, fmt: str, full: bool) -> str:
        error = self.error
        if fmt == "github":
            return _formats.github(self.file, self.findings(), error)
        if fmt == "sarif":
            fixes = {f.transform: f.edits for f in place(Path(self.file), self.checked).fixes}
            return _formats.sarif(self.file, _version(), self.findings(), error, fixes)
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


def _load(path: Path, budget: Budget, d: Discovery, args: argparse.Namespace) -> Discovery:
    try:
        with budget.armed():
            if path.suffix == ".sql":
                load_sql(path, d, args.schema, args.dialect, args.semantics)
            else:
                _only_for_sql(args)
                load(path, d)
    except BudgetExceeded as e:
        d.error = e
    return d


def _only_for_sql(args: argparse.Namespace) -> None:
    for flag in ("schema", "dialect", "semantics"):
        if getattr(args, flag, None) is not None:
            raise UsageError(f"--{flag} reads a .sql file; this target is a Python file")


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
    _load(path, budget, d, args)
    return d, Check(d, target, budget, getattr(args, "require_proved", False))


def cmd_check(args: argparse.Namespace) -> int:
    path, target = split_target(args.target)
    if path.is_dir() or path.name == "dbt_project.yml":
        return _dbt(args, path)
    if path.suffix == ".sql" and (args.fix or args.diff or args.against_sink):
        raise UsageError("--fix, --diff and --against-sink read a Python file; this is a .sql file")
    d, check = _check_file(args, path, target)
    if args.against_sink:
        with check.budget.armed():
            check.compare_sinks()
    if not (args.fix or args.diff):
        return _show(args, check)
    plan = place(path, check.checked)
    # As bytes: `place` keeps the file's line endings, which a text-mode read
    # or write would translate (`\r\n` to `\n`, `\n` to `\r\n` on Windows).
    before = path.read_bytes().decode("utf-8")
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
        path.write_text(plan.text, encoding="utf-8", newline="")
        _, check = _check_file(args, path, target)
    extra = {
        "fixes": [
            {
                "transform": f.transform,
                "requires": f.conditions,
                "placed": f.placed,
                "why": f.why,
            }
            for f in plan.fixes
        ],
        "diff": diff,
        "applied": applied,
    }
    lines = []
    if not plan.fixes:
        other = [
            f"  {c.name}: {h}"
            for c in check.checked
            if c.report is not None
            for h in dict.fromkeys(c.report._all_hints())
        ]
        if other:
            lines.append(
                "No preconditions to add (nothing in `requires` rules these out); "
                "the reports suggest:"
            )
            lines += other
        else:
            lines.append("No preconditions to add: no proof in the file needs one.")
    for f in plan.fixes:
        lines += [f"{f.transform}: requires {p}: {', '.join(cs)}" for p, cs in f.conditions.items()]
        if f.why:
            lines.append(f"  not placed: {f.why}")
    if plan.fixes:
        lines.append(NARROWS)
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
    if args.timeout is not None:
        flags += ["--timeout", f"{args.timeout:g}"]
    if args.memory_limit is not None:
        flags += ["--memory-limit", args.memory_limit]
    return subprocess.call([exe, "check", str(project), *flags])


def _outcome_code(outcome: str) -> int:
    return {"quarantined": QUARANTINED, "held": HELD}.get(outcome, OK)


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
    if args.engine == "polars" and os.environ.get("SVERIFY_MEMORY_LIMIT", "").strip():
        # Polars has no memory cap sverify can set (#783): say so once.
        print(
            "note: the memory limit bounds DuckDB and Spark's driver; it does not reach Polars",
            file=sys.stderr,
        )
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
            code, kind = (NOT_PROVED, "not_proved") if unproved else (NO_ROUTE, "refused")
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
                "quarantine": [q.to_dict(examples=args.examples) for q in s.quarantine],
                "route": str(s.route) if s.route is not None else None,
                "write": None
                if w is None
                else {
                    "mode": w.mode,
                    "version": w.version,
                    "inserts": w.inserts,
                    "deletes": w.deletes,
                },
            }
        )
    outcome = done.outcome
    code = _outcome_code(outcome)
    result["outcome"] = outcome
    result["memory_limit"] = args.memory_limit
    if code != OK:
        result["status"] = outcome
    alert = done.alert(rows=args.examples)
    result["alert"] = alert

    def human() -> str:
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
        dest="format",
        choices=FORMATS,
        default="text",
        help="text (the default), json, or for check: github (annotations), sarif",
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
        help="the data engine's memory limit, such as 2GB: DuckDB's, past which it spills "
        "to disk, and Spark's driver memory; it does not reach Polars "
        "(default: $SVERIFY_MEMORY_LIMIT, else each engine's own)",
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
    c.add_argument("target", help="file.py, file.py:<node or transform>, file.sql or a dbt project")
    c.add_argument(
        "--schema",
        metavar="FILE",
        help="for a .sql file: the types of its tables, YAML or JSON, {table: {column: type}}",
    )
    c.add_argument("--dialect", help="for a .sql file: `sverify.sql`'s dialect (its default)")
    c.add_argument(
        "--semantics",
        help="for a .sql file: `sverify.sql`'s semantics (its default)",
    )
    c.add_argument("--full", action="store_true", help="print each node's full report")
    fix = c.add_mutually_exclusive_group()
    fix.add_argument(
        "--fix",
        action="store_true",
        help="write the preconditions the proofs need into requires=, then check again; "
        "they narrow the input each node accepts, so its sources must meet them",
    )
    fix.add_argument("--diff", action="store_true", help="show what --fix would write")
    c.add_argument(
        "--require-proved",
        action="store_true",
        help="exit 1 for a node whose postconditions are only checked on the data "
        '(`on_unproved="check"`), as for one that is not proved',
    )
    c.add_argument(
        "--against-sink",
        action="store_true",
        help="compare each stored node's contract with the one its sink last committed: "
        "a committed promise the node no longer proves is contract_weakened (exit 1)",
    )
    c.set_defaults(
        run=cmd_check,
        against_sink=False,
        require_proved=False,
        schema=None,
        dialect=None,
        semantics=None,
    )
    r = sub.add_parser(
        "refresh",
        parents=[common],
        help="run a node and report what changed",
        epilog=EXIT_CODES,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    r.add_argument("target", help="file.py:<node>")
    r.add_argument(
        "--engine", default=None, help="duckdb, polars or spark (default: the default engine)"
    )
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
    r.add_argument(
        "--examples",
        action="store_true",
        help="show the rows that broke a condition: up to 10 per source in the JSON's "
        "quarantine examples, and 5 in the alert (rows of your data; off by default)",
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
    proved, 2 usage error, 3 unsupported, 4 time or memory budget exceeded,
    5 a refresh quarantined rows, 6 error, 7 refused (no route to the
    engine), 8 a refresh held a node."""
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

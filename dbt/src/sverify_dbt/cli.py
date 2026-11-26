"""`sverify-dbt check <project>`: the report of `sverify_dbt.check`."""

from __future__ import annotations

import argparse
import json
import os
import sys
from importlib.metadata import version as _version
from pathlib import Path

from sverify._duckdb import memory_limit_error
from sverify.cli import ExitCode
from sverify.errors import MemoryLimitError, UnsupportedError

from sverify_dbt import formats
from sverify_dbt.check import check
from sverify_dbt.manifest import ProjectError
from sverify_dbt.result import CheckResult

#: The exit codes of `sverify check` (`sverify.cli.ExitCode`), those a dbt check
#: gives: a model refused (`--fail-on refused`) or the check unsupported is 3.
#: This `REFUSED` is a model sverify cannot read, `ExitCode.UNSUPPORTED` (3); it is
#: not `ExitCode.REFUSED` (4), a proved node with no route to the engine.
NOT_PROVED, USAGE, REFUSED, BUDGET, ERROR = (
    ExitCode.NOT_PROVED,
    ExitCode.USAGE,
    ExitCode.UNSUPPORTED,
    ExitCode.BUDGET,
    ExitCode.ERROR,
)


def _hard_stop() -> None:
    """The check did not stop in time: end the process."""
    print("sverify-dbt: time budget exceeded", file=sys.stderr)
    os._exit(BUDGET)


def _timeout_asked(arg: float | None) -> bool:
    """Whether `--timeout` or `$SVERIFY_TIMEOUT` sets a time budget."""
    return arg is not None or bool(os.environ.get("SVERIFY_TIMEOUT", "").strip())


def _render(result: CheckResult, fmt: str, code: int = 0) -> str:
    if fmt == "json":
        return json.dumps(result.to_dict(code), indent=2)
    if fmt == "github":
        return formats.github(result)
    if fmt == "sarif":
        return formats.sarif(result, _version("sverify-dbt"))
    if fmt == "junit":
        return formats.junit(result)
    return str(result)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="sverify-dbt",
        description="Prove a dbt project's tests and contracts with sverify, "
        "before the models run.",
    )
    sub = parser.add_subparsers(dest="command", required=True)
    c = sub.add_parser(
        "check",
        help="check the tests and contracts of a compiled project",
        description="Check the tests and contracts of a dbt project. Run `dbt compile` first: "
        "this reads target/manifest.json, and target/catalog.json if there is one.",
    )
    c.add_argument("project", nargs="?", default=".", help="the dbt project's directory")
    c.add_argument("--target-path", default="target", help="the target directory (default target)")
    c.add_argument("--select", "-s", nargs="+", metavar="MODEL", help="models to report on")
    c.add_argument(
        "--format",
        dest="format",
        choices=["text", "json", "github", "sarif", "junit"],
        default="text",
        help="text (the default), json, or for CI: github (annotations), sarif, junit",
    )
    c.add_argument(
        "--json", dest="format", action="store_const", const="json", help="--format json"
    )
    c.add_argument(
        "--selectors",
        nargs="?",
        const="selectors.yml",
        metavar="FILE",
        help="add the selector sverify_proved (the proved tests) to FILE, relative to the "
        "project (default selectors.yml), for `dbt build --exclude selector:sverify_proved`",
    )
    c.add_argument(
        "--counterexamples",
        type=int,
        default=200,
        metavar="N",
        help="small inputs to try per unproved test (default 200; 0 skips the search)",
    )
    c.add_argument(
        "--timeout",
        type=float,
        default=None,
        help="seconds for the whole project check (default: $SVERIFY_TIMEOUT, else no limit); "
        "exit 4 past it",
    )
    c.add_argument(
        "--memory-limit",
        default=None,
        help="DuckDB's memory limit, such as 2GB, past which it spills to disk "
        "(default: $SVERIFY_MEMORY_LIMIT, else DuckDB's own); exit 4 past it",
    )
    c.add_argument(
        "--fail-on",
        choices=["contract", "unproved", "refused", "never"],
        default="contract",
        help="exit 1 on a contract that does not match or a constraint not proved "
        "(contract, the default); unproved: also on any test not proved; refused: all of "
        "that, and exit 3 when a model was refused (sverify cannot read it); or never",
    )
    g = sub.add_parser(
        "suggest",
        help="print the tests sverify suggests adding, as dbt YAML",
        description="Check the project, then print the tests that would let sverify prove "
        "more, as a dbt properties file to merge into the project's YAML: what each model "
        "needs, and the input tests under which an unproved test would hold.",
    )
    g.add_argument("project", nargs="?", default=".", help="the dbt project's directory")
    g.add_argument("--target-path", default="target", help="the target directory (default target)")
    g.add_argument("--select", "-s", nargs="+", metavar="MODEL", help="models to check")
    g.add_argument("--output", "-o", metavar="FILE", help="write the YAML to FILE")
    args = parser.parse_args(argv)
    if args.command == "check" and args.selectors and args.select:
        parser.error("--selectors needs a check of the whole project: drop --select")
    if args.command == "suggest":
        return _suggest(args)
    from sverify.cli import _limits

    try:
        _limits.memory_limit_from(args.memory_limit)
        # Off unless asked for: a project check is many models, and no limit
        # existed before; `sverify check`'s 30 s is per file.
        seconds = _limits.timeout_from(args.timeout) if _timeout_asked(args.timeout) else 0.0
        budget = _limits.Budget(seconds, _hard_stop)
        with budget.armed():
            result = check(
                args.project,
                target_path=args.target_path,
                select=args.select,
                counterexamples=args.counterexamples,
            )
    except _limits.BudgetExceeded as e:
        return _fail(BUDGET, "timeout", e, args)
    except UnsupportedError as e:
        return _fail(REFUSED, "unsupported", e, args)
    except (ProjectError, ValueError) as e:
        return _fail(USAGE, "usage", e, args)
    except Exception as e:
        # sverify raises MemoryLimitError; the project's own DuckDB connection,
        # which describes the project's models, raises DuckDB's error.
        if isinstance(e, MemoryLimitError):
            return _fail(BUDGET, "memory", e, args)
        if memory_limit_error(e, "run") is not None:
            msg = (
                f"DuckDB ran out of memory describing the project's models ({e}): "
                "raise SVERIFY_MEMORY_LIMIT or --memory-limit (such as 4GB)"
            )
            return _fail(BUDGET, "memory", e, args, msg)
        return _fail(ERROR, "error", e, args, f"error: {type(e).__name__}: {e}")
    code = _exit_code(result, args.fail_on)
    print(_render(result, args.format, code))
    if args.fail_on != "never":
        for m in result.refused_contracts:
            print(
                f"sverify-dbt: {m.name} has an enforced contract that was not checked: "
                f"the model was refused ({m.refused})",
                file=sys.stderr,
            )
    if args.selectors:
        path = result.write_selectors(Path(args.project) / args.selectors)
        n = len({t.name for t in result.skippable})
        print(
            f"\nwrote the selector sverify_proved ({n} test(s)) to {path}; run "
            "`dbt build --exclude selector:sverify_proved` to skip them",
            file=sys.stderr,
        )
    return code


def _fail(
    code: int, kind: str, e: BaseException, args: argparse.Namespace, message: str | None = None
) -> int:
    """Report a failed check: a line on stderr and, under `--format json`, the
    envelope with its `error` (`cli.schema.json`) on stdout."""
    message = message or str(e)
    print(f"sverify-dbt: {message}", file=sys.stderr)
    if args.format == "json":
        from importlib.metadata import version

        from sverify_dbt.result import EXIT_STATUS

        err = {"code": kind, "type": type(e).__name__, "message": message}
        doc = {
            "format": 2,
            "sverify": version("sverify"),
            "command": "check",
            "exit": code,
            "status": EXIT_STATUS[code],
            "file": args.project,
            "error": err,
        }
        print(json.dumps(doc, indent=2))
    return code


def _exit_code(result: CheckResult, fail_on: str) -> int:
    """1 where something is not proved (`--fail-on`), else 3 where a model is
    refused and `--fail-on refused` asks, else 0. A refused model's tests are
    not checked, and its reason is the refusal; but a refused model with an
    enforced contract fails the contract gate, since its contract is unchecked
    (#1995)."""
    if fail_on == "never":
        return 0
    failed = bool(result.contract_errors or result.unproved_constraints or result.refused_contracts)
    if fail_on in ("unproved", "refused"):
        failed = failed or any(
            m.by_status("not_proved") or (not m.refused and m.by_status("not_checked"))
            for m in result.models
        )
    if failed:
        return NOT_PROVED
    if fail_on == "refused" and any(m.refused for m in result.models):
        return REFUSED
    return 0


def _suggest(args: argparse.Namespace) -> int:
    try:
        result = check(
            args.project, target_path=args.target_path, select=args.select, counterexamples=0
        )
    except (ProjectError, ValueError) as e:
        print(f"sverify-dbt: {e}", file=sys.stderr)
        return 2
    text = result.suggestions_yaml()
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
        n = len(result.suggestions())
        print(f"wrote {n} suggested test(s) to {args.output}", file=sys.stderr)
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main())

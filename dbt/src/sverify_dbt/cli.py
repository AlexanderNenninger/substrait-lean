"""`sverify-dbt check <project>`: the report of `sverify_dbt.check`."""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

import sverify
from sverify.errors import UnsupportedError

import sverify_dbt
from sverify_dbt import formats
from sverify_dbt.check import check
from sverify_dbt.manifest import ProjectError
from sverify_dbt.result import CheckResult

#: The exit codes of `sverify check`: 0 holds, 1 not proved, 2 usage, 3 a model
#: refused (`--fail-on refused`) or the check unsupported, 4 a budget, 6 an error.
NOT_PROVED, USAGE, REFUSED, BUDGET, ERROR = 1, 2, 3, 4, 6


def _hard_stop() -> None:
    """The check did not stop in time: end the process."""
    print("sverify-dbt: time budget exceeded", file=sys.stderr)
    os._exit(BUDGET)


def _timeout_asked(arg: float | None) -> bool:
    """Whether `--timeout` or `$SVERIFY_TIMEOUT` sets a time budget."""
    return arg is not None or bool(os.environ.get("SVERIFY_TIMEOUT", "").strip())


def _fail(args: argparse.Namespace, code: int, kind: str, e: BaseException | str) -> int:
    """Say what stopped the check on stderr, and as the JSON document's `error`."""
    message = str(e)
    print(f"sverify-dbt: {message}", file=sys.stderr)
    if args.format == "json":
        err = {
            "code": kind,
            "type": type(e).__name__ if not isinstance(e, str) else kind,
            "message": message,
        }
        print(json.dumps(formats.envelope(None, code, sverify.__version__, err), indent=2))
    return code


def _render(result: CheckResult, fmt: str, code: int = 0) -> str:
    if fmt == "json":
        return json.dumps(formats.envelope(result, code, sverify.__version__), indent=2)
    if fmt == "github":
        return formats.github(result)
    if fmt == "sarif":
        return formats.sarif(result, sverify_dbt.__version__)
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
        "--output-format",
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
        "(contract, the default); unproved: also on any test not proved; refused: also "
        "exit 3 when a model was refused (sverify cannot read it); or never",
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
        return _fail(args, BUDGET, "memory" if e.what == "memory" else "timeout", e)
    except UnsupportedError as e:
        return _fail(args, REFUSED, "unsupported", e)
    except (ProjectError, ValueError) as e:
        return _fail(args, USAGE, "usage", e)
    except Exception as e:
        if _limits.is_out_of_memory(e):
            return _fail(args, BUDGET, "memory", f"memory budget exceeded ({e})")
        return _fail(args, ERROR, "error", f"error: {type(e).__name__}: {e}")
    code = _exit_code(result, args.fail_on)
    print(_render(result, args.format, code))
    if args.selectors:
        path = result.write_selectors(Path(args.project) / args.selectors)
        n = len({t.name for t in result.skippable})
        print(
            f"\nwrote the selector sverify_proved ({n} test(s)) to {path}; run "
            "`dbt build --exclude selector:sverify_proved` to skip them",
            file=sys.stderr,
        )
    return code


def _exit_code(result: CheckResult, fail_on: str) -> int:
    """1 where something is not proved (`--fail-on`), else 3 where a model is
    refused and `--fail-on refused` asks, else 0. A refused model's tests and
    constraints are not checked, and its reason is the refusal, not a failed
    gate (#891, 1.3)."""
    if fail_on == "never":
        return 0
    failed = bool(result.contract_errors or result.unproved_constraints)
    if fail_on == "unproved":
        failed = failed or any(
            m.by_status("not proved") or (not m.refused and m.by_status("not checked"))
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
        Path(args.output).write_text(text)
        n = len(result.suggestions())
        print(f"wrote {n} suggested test(s) to {args.output}", file=sys.stderr)
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main())

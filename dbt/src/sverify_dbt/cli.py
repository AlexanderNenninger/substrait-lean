"""`sverify-dbt check <project>`: the report of `sverify_dbt.check`."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from sverify_dbt.check import check
from sverify_dbt.manifest import ProjectError


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
    c.add_argument("--json", action="store_true", help="print the result as JSON")
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
        "--fail-on",
        choices=["contract", "unproved", "never"],
        default="contract",
        help="exit with status 1 on a contract that does not match or a constraint not "
        "proved (contract, the default), also on any test not proved or model refused "
        "(unproved), or never",
    )
    args = parser.parse_args(argv)
    try:
        result = check(
            args.project,
            target_path=args.target_path,
            select=args.select,
            counterexamples=args.counterexamples,
        )
    except (ProjectError, ValueError) as e:
        print(f"sverify-dbt: {e}", file=sys.stderr)
        return 2
    print(json.dumps(result.to_dict(), indent=2) if args.json else result)
    if args.selectors:
        path = result.write_selectors(Path(args.project) / args.selectors)
        n = len({t.name for t in result.proved})
        print(
            f"\nwrote the selector sverify_proved ({n} test(s)) to {path}; run "
            "`dbt build --exclude selector:sverify_proved` to skip them",
            file=sys.stderr,
        )
    failed = bool(result.contract_errors or result.unproved_constraints)
    if args.fail_on == "unproved":
        failed = failed or any(
            m.refused or m.by_status("not proved") or m.by_status("not checked")
            for m in result.models
        )
    return 1 if failed and args.fail_on != "never" else 0


if __name__ == "__main__":
    sys.exit(main())

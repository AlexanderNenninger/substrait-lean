"""`python -m sverify_vscode check FILE` prints a file's check as JSON;
`python -m sverify_vscode serve` answers requests on stdin (`server`)."""

import json
import sys


def main() -> None:
    args = sys.argv[1:]
    if args[:1] == ["serve"]:
        from .server import main as serve

        serve()
    elif args[:1] == ["check"] and len(args) >= 2:
        from .check import check

        real = sys.stdout
        sys.stdout = sys.stderr
        n = int(args[2]) if len(args) > 2 else None
        real.write(json.dumps(check(args[1], n), indent=1, default=str) + "\n")
    else:
        sys.exit("usage: python -m sverify_vscode check FILE [COUNTEREXAMPLES] | serve")


main()

"""`sverify contract export <file>:<node> --format odcs` (#791): a node's
contract in a standard format, on standard output or in a file."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

FORMATS = ("odcs",)


def add_parser(sub: argparse._SubParsersAction) -> None:
    """Add `contract export` to the command's subparsers."""
    c = sub.add_parser("contract", help="export a node's contract in a standard format")
    actions = c.add_subparsers(dest="action", required=True)
    e = actions.add_parser(
        "export",
        help="write a node's contract as ODCS (Open Data Contract Standard)",
        description="Write the contract of <file>:<node> as an ODCS v3.2.0 document: "
        "YAML on standard output, or to --output (JSON for a .json file). "
        "Rules carry the custom property `sverify` with their status: proved, "
        "checked on the data, or declared.",
    )
    e.add_argument("target", help="file.py:<node>")
    e.add_argument("--format", dest="contract_format", choices=FORMATS, default="odcs")
    e.add_argument("--output", "-o", default=None, help="the file to write (default: stdout)")
    e.add_argument("--id", default=None, help="the contract's id (default: from the node's name)")
    e.add_argument("--version", dest="contract_version", default="1.0.0")
    e.set_defaults(run=cmd_export, format="text", full=False, timeout=None, memory_limit=None)


def cmd_export(args: argparse.Namespace) -> int:
    from sverify import odcs
    from sverify.cli._common import OK, UsageError, split_target
    from sverify.cli._discover import Discovery, load

    path, target = split_target(args.target)
    if target is None:
        raise UsageError("sverify contract export takes <file>:<node>")
    if not path.is_file():
        raise UsageError(f"{path}: no such file")
    d = Discovery(path)
    load(path, d)
    if d.error is not None:
        raise d.error
    node = d.nodes.get(target)
    if node is None:
        have = ", ".join(sorted(d.nodes)) or "none"
        raise UsageError(f"{path} has no node {target!r}; it has {have}")
    doc = odcs.export(node, id=args.id, version=args.contract_version)
    out = args.output
    if out is None:
        sys.stdout.write(odcs.dumps(doc, "yaml"))
    else:
        Path(out).write_text(odcs.dumps(doc, "json" if out.endswith(".json") else "yaml"))
    return OK

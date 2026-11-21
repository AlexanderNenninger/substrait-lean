"""The coverage summary of CI's `coverage` job (#750), as Markdown.

Reads the JSON that `coverage json` writes for the combined shards and prints
the line and the line-and-branch coverage of `sverify` and the modules with the
most missed lines. The gate warns: it prints a warning annotation under the
target and always exits 0.

    python scripts/coverage_summary.py coverage.json [--target 89] [--top 10] [--package sverify]
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def summarise(data: dict, target: float, top: int, package: str = "sverify") -> tuple[str, bool]:
    """The Markdown report and whether the combined number meets `target`."""
    files = {
        name: f["summary"]
        for name, f in data["files"].items()
        if f"/{package}/" in name.replace("\\", "/") or name.startswith(f"{package}/")
    }
    stmts = sum(s["num_statements"] for s in files.values())
    missed = sum(s["missing_lines"] for s in files.values())
    branches = sum(s.get("num_branches", 0) for s in files.values())
    partial = sum(s.get("missing_branches", 0) for s in files.values())
    lines = 100 * (stmts - missed) / stmts if stmts else 0.0
    # coverage.py's `percent_covered`: (covered lines + covered branches) over
    # (statements + branches).
    combined = 100 * (stmts - missed + branches - partial) / (stmts + branches) if stmts else 0.0
    ok = combined >= target
    out = [
        f"### Coverage of `{package}`",
        "",
        f"- lines: {lines:.1f} % ({stmts - missed} of {stmts} statements)",
        f"- lines and branches: {combined:.1f} % (target {target:g} %)",
        "",
        f"The {top} modules with the most missed lines:",
        "",
        "| module | missed | statements | line % |",
        "|---|---:|---:|---:|",
    ]
    worst = sorted(files.items(), key=lambda kv: -kv[1]["missing_lines"])[:top]
    for name, s in worst:
        n = s["num_statements"]
        pct = 100 * (n - s["missing_lines"]) / n if n else 100.0
        out.append(f"| `{name}` | {s['missing_lines']} | {n} | {pct:.1f} |")
    return "\n".join(out) + "\n", ok


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("json", type=Path)
    p.add_argument("--target", type=float, default=89.0)
    p.add_argument("--top", type=int, default=10)
    p.add_argument("--package", default="sverify", help="the package to report (default sverify)")
    args = p.parse_args(argv)
    text, ok = summarise(json.loads(args.json.read_text()), args.target, args.top, args.package)
    print(text)
    if not ok:
        print(f"::warning::coverage of {args.package} is under {args.target:g} %", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

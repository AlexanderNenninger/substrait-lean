"""The axioms column of `docs/trusted-base.md` (#1088).

`SubstraitLean/Examples.lean` prints `#print axioms` of the main theorems.
This fills each row of the page's kernel-checked table (between
`<!-- axioms:start -->` and `<!-- axioms:end -->`) with what Lean prints for
its theorem, from a build that checks the generated proofs
(`lake -R -Kcheck_generated=true build`): with them unchecked, the theorems
over the generated entries show `sorryAx`.

    python -m sverify_dev.trusted_base --write   # rewrite the column
    python -m sverify_dev.trusted_base --check   # fail where it drifted

`--from FILE` reads Lean's output from a file instead of running
`lake env lean SubstraitLean/Examples.lean`.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PAGE = ROOT / "docs" / "trusted-base.md"
EXAMPLES = "SubstraitLean/Examples.lean"
START, END = "<!-- axioms:start -->", "<!-- axioms:end -->"
#: Lean's output for one theorem: its name and its axioms, over several lines.
PRINTED = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]", re.S)
#: A row of the table: its theorem, between backticks, in the first cell.
ROW = re.compile(r"^\| `([^`]+)` \|(.*)\| ([^|]*) \|$")


def printed(text: str) -> dict[str, str]:
    """Each theorem Lean printed, with its axioms as the page writes them."""
    return {m[1]: ", ".join(m[2].split()).replace(",,", ",") for m in PRINTED.finditer(text)}


def lean_output() -> str:
    out = subprocess.run(
        ["lake", "env", "lean", EXAMPLES], cwd=ROOT, capture_output=True, text=True, check=False
    )
    if out.returncode != 0:
        sys.exit(f"lake env lean {EXAMPLES} failed:\n{out.stderr or out.stdout}")
    return out.stdout


def filled(page: str, axioms: dict[str, str]) -> str:
    """`page` with each table row's axioms cell from `axioms`."""
    head, rest = page.split(START, 1)
    table, tail = rest.split(END, 1)
    rows = []
    for line in table.split("\n"):
        m = ROW.match(line)
        if m and m[1] != "Theorem":
            name = f"Substrait.{m[1]}"
            if name not in axioms:
                sys.exit(f"{EXAMPLES} prints no `#print axioms {name}`")
            line = f"| `{m[1]}` |{m[2]}| {axioms[name]} |"
        rows.append(line)
    return head + START + "\n".join(rows) + END + tail


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    ap.add_argument("--from", dest="source", type=Path)
    args = ap.parse_args(argv)
    text = args.source.read_text() if args.source else lean_output()
    page = PAGE.read_text()
    new = filled(page, printed(text))
    if args.write:
        PAGE.write_text(new)
        return 0
    if new != page:
        print(
            "docs/trusted-base.md's axioms column differs from what Lean prints: "
            "run `poe trusted-base` after `lake -R -Kcheck_generated=true build`",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

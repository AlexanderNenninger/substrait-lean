"""Check that expected results moved by ulps only (D25, #915).

Compares each file against its version at a git ref, number by number: every
double that changed must be within `--ulps` units in the last place of the new
value (4 by default). Files whose numbers differ in count or that change
anything other than numbers are reported as structural changes. Run it after
regenerating goldens or the catalogue:

    python python/scripts/ulp_check.py --ref origin/main \
        tests/fixtures/*.expected catalogue/status.json

Exit status 1 when a number moved by more than the bound or a file changed
structurally; the output lists each changed number with its distance in ulps.
"""

from __future__ import annotations

import argparse
import math
import re
import subprocess
import sys
from pathlib import Path

NUMBER = re.compile(r"-?(?:\d+\.\d*|\.\d+|\d+)(?:[eE][-+]?\d+)?|-?inf|nan")


def numbers(text: str) -> tuple[list[str], str]:
    """The numbers in `text`, and the text with each replaced by `#`."""
    return NUMBER.findall(text), NUMBER.sub("#", text)


def ulps(old: float, new: float) -> float:
    """`|old - new|` in units of the last place of `new`."""
    if old == new or (math.isnan(old) and math.isnan(new)):
        return 0.0
    if not (math.isfinite(old) and math.isfinite(new)):
        return math.inf
    return abs(old - new) / math.ulp(new)


def check(path: Path, ref: str, bound: float) -> list[str]:
    try:
        before = subprocess.run(
            ["git", "show", f"{ref}:{path.as_posix()}"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout
    except subprocess.CalledProcessError:
        return []  # new file: nothing to compare
    after = path.read_text()
    if before == after:
        return []
    (old, shape_old), (new, shape_new) = numbers(before), numbers(after)
    if shape_old != shape_new or len(old) != len(new):
        return [f"{path}: structural change (not only numbers)"]
    problems = []
    for a, b in zip(old, new, strict=True):
        if a == b:
            continue
        d = ulps(float(a), float(b))
        line = f"{path}: {a} -> {b} ({d:.1f} ulp)"
        print(line)
        if d > bound:
            problems.append(line + f": more than {bound:g} ulp")
    return problems


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("files", nargs="+", type=Path)
    parser.add_argument("--ref", default="origin/main", help="git ref to compare with")
    parser.add_argument("--ulps", type=float, default=4.0, help="largest allowed move")
    args = parser.parse_args(argv)
    problems = [p for f in args.files for p in check(f, args.ref, args.ulps)]
    for p in problems:
        print(p, file=sys.stderr)
    changed = sum(1 for f in args.files if check_changed(f, args.ref))
    print(f"{len(args.files)} files checked, {changed} changed, {len(problems)} problems")
    return 1 if problems else 0


def check_changed(path: Path, ref: str) -> bool:
    r = subprocess.run(["git", "diff", "--quiet", ref, "--", str(path)], capture_output=True)
    return r.returncode != 0


if __name__ == "__main__":
    sys.exit(main())

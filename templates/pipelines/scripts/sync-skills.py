"""Copy the agent skills of the installed sverify into .claude/skills/, so a
Claude Code session in this repository knows sverify's API. Run it after
upgrading sverify; `--check` exits 1 when the copies differ.

    python scripts/sync-skills.py [--check]
"""

from __future__ import annotations

import sys
from importlib.resources import files
from pathlib import Path

SKILLS = ("sverify", "sverify-pipelines", "sverify-engines")
DEST = Path(__file__).resolve().parent.parent / ".claude" / "skills"


def tree(root) -> dict[str, bytes]:
    out: dict[str, bytes] = {}
    stack = [(root, "")]
    while stack:
        node, prefix = stack.pop()
        for child in node.iterdir():
            rel = f"{prefix}{child.name}"
            if child.is_dir():
                stack.append((child, rel + "/"))
            else:
                out[rel] = child.read_bytes()
    return out


def main() -> int:
    check = "--check" in sys.argv[1:]
    stale = []
    for name in SKILLS:
        want = tree(files("sverify") / "skills" / name)
        have = tree(DEST / name) if (DEST / name).is_dir() else {}
        if want == have:
            continue
        stale.append(name)
        if not check:
            for rel in set(have) - set(want):
                (DEST / name / rel).unlink()
            for rel, data in want.items():
                path = DEST / name / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
    if check and stale:
        print(f"stale skills: {', '.join(stale)}; run python scripts/sync-skills.py")
        return 1
    print("skills up to date" if not stale else f"updated: {', '.join(stale)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

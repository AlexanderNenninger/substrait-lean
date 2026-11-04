"""Where Substrait's choices and the reference's differ (#444, step 2).

`substrait-check --profile-diff` lists the options where `Profile.substrait`
and `Profile.reference` (`SubstraitLean/SubstraitProfile.lean`) accept other
preferences from a plan, or allow other behaviours where the plan states none.
This module renders it as the table of `docs/core-semantics.md`'s "The
Substrait profile", between its markers; `tests/test_substrait_profile.py`
fails while the published table is stale.

    python -m sverify_dev.profile_diff            # print the table
    python -m sverify_dev.profile_diff --write    # rewrite the doc's table
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

DOC = Path(__file__).resolve().parents[3] / "docs" / "core-semantics.md"
START, END = "<!-- substrait-diff:start -->", "<!-- substrait-diff:end -->"


def rows() -> list[dict[str, Any]]:
    """The checker's diff rows."""
    from sverify.engine import checker_path

    out = subprocess.run(
        [str(checker_path()), "--profile-diff"], capture_output=True, text=True, check=True
    )
    return json.loads(out.stdout)


def _cell(side: dict[str, Any]) -> str:
    """What a profile accepts from a plan, and allows where it states nothing."""

    def names(bs: list[str]) -> str:
        return ", ".join(f"`{b}`" for b in bs) or "refused"

    accepts, default = side["accepts"], side["default"]
    if accepts is None:
        return f"any preference; {names(default)} by default"
    if sorted(accepts) == sorted(default):
        return names(default)
    return f"{names(accepts)}; {names(default)} by default"


def table(rs: list[dict[str, Any]]) -> str:
    lines = [
        "| Option | Group | Substrait | Reference | Reference's tool |",
        "|---|---|---|---|---|",
    ]
    for r in rs:
        group = f"`{r['group']}`" if r["group"] else "all others"
        tool = (r["tool"] or "").replace("_", " ")
        lines.append(
            f"| `{r['option']}` | {group} | {_cell(r['substrait'])} | "
            f"{_cell(r['reference'])} | {tool} |"
        )
    return "\n".join(lines)


def published(text: str | None = None) -> str:
    """The table between the doc's markers."""
    text = DOC.read_text() if text is None else text
    m = re.search(re.escape(START) + r"\n?(.*?)\n?" + re.escape(END), text, re.S)
    if m is None:
        raise ValueError(f"{DOC} has no {START} … {END} block")
    return m.group(1)


def write(rs: list[dict[str, Any]]) -> None:
    text = DOC.read_text()
    published(text)
    pattern = re.compile(re.escape(START) + ".*?" + re.escape(END), re.S)
    DOC.write_text(pattern.sub(lambda _: f"{START}\n{table(rs)}\n{END}", text))


def main() -> None:
    rs = rows()
    if "--write" in sys.argv:
        write(rs)
    else:
        print(table(rs))


if __name__ == "__main__":
    main()

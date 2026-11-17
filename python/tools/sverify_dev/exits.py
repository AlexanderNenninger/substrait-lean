"""Where sverify refuses, and whether the message names an exit (#1205).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of
sverify's API.

The 1.0 gate says every refusal names the issue or option that lifts it. The
contract census (`contract_census`) covers the routes; this covers the
`raise` sites of `python/src/sverify`: each `raise` of an exception of the
`SverifyError` family (`Unsupported`, `RouteError`, `ExportError`, `Refused`,
...) or of a refusal helper. A site's message is the text of its first
argument with every formatted part written `{}`.

A message names an exit when it points at an issue or a link, or tells the
user what to do with a thing it names (`use`, `write`, `run`, `state`, ...
followed by a code span, an argument or a call). It gives a hint when it
says what is accepted (`only`, `must`, `needs`, `; ...`). The rest is
unnamed. `python -m sverify_dev.exits` prints the counts per module and
`--sites` the unnamed sites; `tests/test_exits.py` keeps them from rising
(`tests/exits_baseline.json`).
"""

from __future__ import annotations

import ast
import collections
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

SRC = Path(__file__).resolve().parents[2] / "src" / "sverify"
BASELINE = Path(__file__).resolve().parents[2] / "tests" / "exits_baseline.json"

#: The classes every refusal derives from, by name, and the helpers that build one.
_ROOTS = {"SverifyError", "UnsupportedError", "Unsupported", "Refused", "ProducerRefused"}
_HELPER = re.compile(r"refus|unsupported", re.I)
#: Classes whose message always ends with an action (`SqlUnsupported` adds a
#: rewrite, or "write this step in Ibis").
_OWN_EXIT = {"SqlUnsupported", "WriterUnsupported", "refused"}

_VERBS = (
    "use|set|pass|write|run|add|declare|install|call|state|choose|give|say|rewrite|replace|"
    "cast|wrap|drop|remove|pin|enable|try|switch|upgrade|read|select|take|order|name|put|"
    "build|compare|re-run|change"
)
EXIT = re.compile(
    r"#\d+|https?://|\bsee [A-Za-z`]|DUCKDB_ONLY|ISSUE_271|to_sql\(|"
    rf"(?:; |, or )({_VERBS})\b|"
    rf"\b({_VERBS})\b[^.]{{0,60}}"
    r"(`|\w+=|\(\)|first|instead|\bas \w+|\bin Ibis|another engine|fix it)",
    re.I,
)
HINT = re.compile(r"; [a-z]|\bonly\b|\binstead\b|\bmust\b|\bneeds?\b|\bexpects?\b|\bunless\b", re.I)


@dataclass(frozen=True)
class Site:
    file: str
    line: int
    cls: str
    message: str

    @property
    def tier(self) -> str:
        if self.cls in _OWN_EXIT or EXIT.search(self.message):
            return "exit"
        return "hint" if HINT.search(self.message) else "unnamed"


def _text(node: ast.AST, consts: dict[str, str]) -> str:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    if isinstance(node, ast.JoinedStr):
        return "".join(
            _text(v, consts)
            if isinstance(v, ast.Constant)
            else _text(v.value, consts)
            if isinstance(v, ast.FormattedValue)
            and isinstance(v.value, ast.Name)
            and v.value.id in consts
            else "{}"
            for v in node.values
        )
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add | ast.Mod):
        return _text(node.left, consts) + _text(node.right, consts)
    if isinstance(node, ast.Name):
        return consts.get(node.id, "{" + node.id + "}")
    if (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "format"
    ):
        return _text(node.func.value, consts)
    return "{}"


def sites(root: Path = SRC) -> list[Site]:
    """Every refusal `raise` under `root`."""
    trees = {
        p: ast.parse(p.read_text())
        for p in sorted(root.rglob("*.py"))
        if "__pycache__" not in p.parts
    }
    bases: dict[str, list[str]] = {}
    for tree in trees.values():
        for n in ast.walk(tree):
            if isinstance(n, ast.ClassDef):
                bases[n.name] = [
                    b.id if isinstance(b, ast.Name) else getattr(b, "attr", "") for b in n.bases
                ]

    def refusal(name: str, seen: tuple[str, ...] = ()) -> bool:
        if name in _ROOTS:
            return True
        return any(refusal(b, (*seen, name)) for b in bases.get(name, []) if b not in seen)

    out: list[Site] = []
    for p, tree in trees.items():
        consts: dict[str, str] = {}
        for n in ast.walk(tree):
            if (
                isinstance(n, ast.Assign)
                and len(n.targets) == 1
                and isinstance(n.targets[0], ast.Name)
                and isinstance(n.value, ast.Constant | ast.JoinedStr)
            ):
                consts[n.targets[0].id] = _text(n.value, consts)
        for n in ast.walk(tree):
            if not (isinstance(n, ast.Raise) and isinstance(n.exc, ast.Call)):
                continue
            f = n.exc.func
            name = f.id if isinstance(f, ast.Name) else getattr(f, "attr", "")
            if not (refusal(name) or _HELPER.search(name)):
                continue
            msg = _text(n.exc.args[0], consts) if n.exc.args else ""
            if not msg.strip() or msg.strip() == "{}":
                msg = " ".join(
                    _text(k.value, consts)
                    for k in n.exc.keywords
                    if k.arg in ("message", "reason", "msg")
                )
            out.append(Site(str(p.relative_to(root)), n.lineno, name, msg.strip()))
    return out


def unnamed_by_file(found: list[Site] | None = None) -> dict[str, int]:
    """The count of sites that name no exit and give no hint, per file."""
    counts = collections.Counter(s.file for s in (found or sites()) if s.tier == "unnamed")
    return dict(sorted(counts.items()))


def main() -> None:
    found = sites()
    mods: dict[str, collections.Counter[str]] = collections.defaultdict(collections.Counter)
    for s in found:
        parts = s.file.split("/")
        mods["/".join(parts[:2]) if len(parts) > 2 else parts[0]][s.tier] += 1
    print(f"{'module':28} {'total':>5} {'exit':>5} {'hint':>5} {'unnamed':>7}")
    for m, c in sorted(mods.items(), key=lambda kv: -sum(kv[1].values())):
        print(f"{m:28} {sum(c.values()):5} {c['exit']:5} {c['hint']:5} {c['unnamed']:7}")
    total = collections.Counter(s.tier for s in found)
    print(f"{'total':28} {len(found):5} {total['exit']:5} {total['hint']:5} {total['unnamed']:7}")
    if "--sites" in sys.argv:
        for s in found:
            if s.tier == "unnamed":
                print(f"{s.file}:{s.line} {s.cls}: {s.message}")
    if "--write-baseline" in sys.argv:
        BASELINE.write_text(json.dumps(unnamed_by_file(found), indent=2) + "\n")


if __name__ == "__main__":
    main()

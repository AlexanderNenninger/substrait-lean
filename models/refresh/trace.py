"""Print a TLC counterexample of Refresh.tla as one short line per step.

    python models/refresh/trace.py <TLC output file>

Reads the trace TLC prints after a violation (the states, with the action
that led to each) and shows what changed at each step: the source, the
sink's table, the commits added to its log, each writer and the zombie
writes in flight.
"""

from __future__ import annotations

import re
import sys
from typing import Any

_TOKEN = re.compile(
    r'\s*(<<|>>|\|->|:>|@@|"(?:[^"\\]|\\.)*"|-?\d+|[A-Za-z_][A-Za-z0-9_]*|[\[\](){},])'
)


def _tokens(text: str) -> list[str]:
    out, pos = [], 0
    text = text.rstrip()
    while pos < len(text):
        m = _TOKEN.match(text, pos)
        if m is None:
            raise ValueError(f"cannot read {text[pos : pos + 20]!r}")
        out.append(m.group(1))
        pos = m.end()
    return out


class _Parser:
    def __init__(self, text: str):
        self.toks, self.i = _tokens(text), 0

    def peek(self) -> str:
        return self.toks[self.i]

    def take(self, want: str | None = None) -> str:
        tok = self.toks[self.i]
        if want is not None and tok != want:
            raise ValueError(f"expected {want}, got {tok}")
        self.i += 1
        return tok

    def items(self, close: str) -> list[Any]:
        out = []
        while self.peek() != close:
            out.append(self.value())
            if self.peek() == ",":
                self.take()
        self.take(close)
        return out

    def value(self) -> Any:
        tok = self.take()
        if tok == "[":
            rec = {}
            while self.peek() != "]":
                key = self.take()
                self.take("|->")
                rec[key] = self.value()
                if self.peek() == ",":
                    self.take()
            self.take("]")
            return rec
        if tok == "<<":
            return self.items(">>")
        if tok == "{":
            return ("set", self.items("}"))
        if tok == "(":
            fn = {}
            while True:
                key = self.take()
                self.take(":>")
                fn[key] = self.value()
                if self.peek() == "@@":
                    self.take()
                    continue
                self.take(")")
                return fn
        if tok.startswith('"'):
            return tok[1:-1]
        if tok in ("TRUE", "FALSE"):
            return tok == "TRUE"
        if re.fullmatch(r"-?\d+", tok):
            return int(tok)
        if self.i < len(self.toks) and self.peek() == ":>":  # a one-point function
            self.take()
            return {tok: self.value()}
        return tok


def parse(text: str) -> Any:
    return _Parser(text).value()


def states(lines: list[str]) -> list[tuple[str, dict[str, Any]]]:
    """The trace's states: the step's label and the variables' values."""
    out: list[tuple[str, dict[str, Any]]] = []
    label, var, buf, current = None, None, [], {}

    def flush() -> None:
        if var is not None:
            current[var] = parse(" ".join(buf))

    for line in lines:
        head = re.match(r"^(State \d+|Back to state \d+): ?(.*)$", line)
        if (
            head
            or line.startswith(("Error:", "Finished", "The number"))
            or re.match(r"^\d+ states generated", line)
        ):
            flush()
            if label is not None:
                out.append((label, current))
            var, buf, current = None, [], {}
            label = None
            if head:
                label = (
                    head.group(1)
                    + " "
                    + re.sub(r" line \d+.*", "", head.group(2)).strip("<>")
                )
                if "Stuttering" in line:
                    out.append((label, {}))
                    label = None
            continue
        if label is None:
            continue
        m = re.match(r"^/\\ (\w+) = (.*)$", line)
        if m:
            flush()
            var, buf = m.group(1), [m.group(2)]
        elif var is not None:
            buf.append(line)
    return out


def show_st(t: dict[str, Any]) -> str:
    return f"P{t['plan']}(c{t['c']})" if t["k"] == "rows" else t["k"]


def show_out(o: dict[str, Any]) -> str:
    on = f" on {show_st(o['written'])}" if o["mode"] == "merge" else ""
    return f"{o['mode']} P{o['plan']} v{o['ver']} {show_st(o['view'])}{on} if epoch={o['read']}"


def show_entry(e: dict[str, Any]) -> str:
    if not e["app"]:
        return "foreign rows"
    return f"{e['mode']} P{e['plan']} v{e['ver']} c{e['c']} (digest {e['dig']}) by {e['by']}"


def show_writer(x: dict[str, Any]) -> str:
    if x["st"] == "down":
        return "down"
    out = f"{x['st']} P{x['plan']} v{x['ver']} view={show_st(x['view'])} written={show_st(x['written'])}"
    if x["pend"]["on"]:
        out += f" pending=P{x['pend']['plan']} v{x['pend']['ver']}"
    if x["st"] == "writing":
        out += f" sending[{show_out(x['out'])}]"
    return out


def render(trace: list[tuple[str, dict[str, Any]]]) -> list[str]:
    lines, before = [], {}
    for label, now in trace:
        if not now:
            lines.append(f"{label}")
            continue
        parts = []
        src = now["src"]
        if before.get("src") != src:
            parts.append(
                f"source c{src['c']}" + (f" v{src['ver']}" if src["ver"] else "")
            )
        if before.get("tbl") != now["tbl"]:
            parts.append(f"table {show_st(now['tbl'])}")
        old = before.get("log", [])
        for e in now["log"][len(old) :]:
            parts.append(f"commit #{now['log'].index(e) + 1}: {show_entry(e)}")
        for s, x in sorted(now["w"].items()):
            if before.get("w", {}).get(s) != x:
                parts.append(f"{s}: {show_writer(x)}")
        if before.get("zombies") != now["zombies"]:
            zs = now["zombies"][1]
            parts.append(
                "zombies: " + ("; ".join(show_out(o) for o in zs) if zs else "none")
            )
        if before.get("deployed") != now["deployed"]:
            parts.append(f"deployed P{now['deployed']}")
        lines.append(f"{label}: " + " | ".join(parts))
        before = now
    return lines


def main() -> None:
    with open(sys.argv[1]) as f:
        text = f.read().splitlines()
    for err in (
        line for line in text if line.startswith("Error:") and "behavior" not in line
    ):
        print(err)
        break
    for line in render(states(text)):
        print(line)


if __name__ == "__main__":
    main()

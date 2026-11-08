"""Plans evaluated by Lean: `Rel.eval` (`lean_rows`, `lean_values`) and
`Rel.evalChoices` (`lean_choices`) on plans whose tables are inlined as
virtual tables (`inline_tables`), and the rows the checker prints read back.
The oracle of the tests and of the counterexample search.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.
"""

from __future__ import annotations

import base64
import datetime as dt
import json
import math
import re
import subprocess
from collections.abc import Callable, Mapping, Sequence
from decimal import ROUND_HALF_UP, Decimal, localcontext

from sverify._checker import decode_double, run_checker

EPOCH = dt.datetime(1970, 1, 1)


def decimal_literal(v: Decimal, precision: int = 38, scale: int | None = None) -> dict:
    """A Substrait decimal literal: the unscaled integer, 16 bytes little-endian.
    Without a `scale`, the value's own; with one, rounded half away from zero."""
    if scale is None:
        exponent = v.as_tuple().exponent
        scale = max(0, -exponent) if isinstance(exponent, int) else 0
    # A context wide enough for 38 digits: the default's 28 would round them.
    with localcontext(prec=80):
        unscaled = int(v.scaleb(scale).to_integral_value(rounding=ROUND_HALF_UP))
    value = base64.b64encode(unscaled.to_bytes(16, "little", signed=True)).decode()
    return {"literal": {"decimal": {"value": value, "precision": precision, "scale": scale}}}


def literal(v: object) -> dict:
    if isinstance(v, Decimal):
        return decimal_literal(v)
    if v is None:
        return {"literal": {"null": {"i64": {}}}}
    if isinstance(v, bool):
        return {"literal": {"boolean": v}}
    if isinstance(v, int):
        return {"literal": {"i64": str(v)}}
    if isinstance(v, str):
        return {"literal": {"string": v}}
    if isinstance(v, dt.datetime):
        micros = (v - EPOCH) // dt.timedelta(microseconds=1)
        return {"literal": {"precisionTimestamp": {"precision": 6, "value": str(micros)}}}
    if isinstance(v, dt.date):
        return {"literal": {"date": (v - EPOCH.date()).days}}
    if isinstance(v, dt.time):
        micros = ((v.hour * 60 + v.minute) * 60 + v.second) * 1_000_000 + v.microsecond
        return {"literal": {"precisionTime": {"precision": 6, "value": str(micros)}}}
    if isinstance(v, float):
        # The model's one zero and one NaN: -0.0 is 0.0, a negative NaN is NaN.
        text = "NaN" if math.isnan(v) else "Infinity" if v == math.inf else "-Infinity"
        return {"literal": {"fp64": v + 0.0 if math.isfinite(v) else text}}
    if isinstance(v, list):
        # Elements are literals without the `literal` key.
        if not v:
            return {"literal": {"emptyList": {"type": {"i64": {}}}}}
        return {"literal": {"list": {"values": [literal(x)["literal"] for x in v]}}}
    if isinstance(v, dict):
        # A struct is its fields, in order (`docs/nested-values.md`).
        return {"literal": {"struct": {"fields": [literal(x)["literal"] for x in v.values()]}}}
    raise TypeError(f"no literal for {v!r}")


def typed_code(t: dict, v: int) -> dict:
    """An integer given as a column's code: a timestamp's or a time's
    microseconds, a date's days, a double's code (`core/Sverify/Core/Float.lean`),
    a decimal's unscaled integer; an integer elsewhere. The model's values
    have their kinds, so a code alone is an integer (#923)."""
    if "precisionTimestamp" in t or "timestamp" in t or "precisionTimestampTz" in t:
        return {"literal": {"precisionTimestamp": {"precision": 6, "value": str(v)}}}
    if "date" in t:
        return {"literal": {"date": v}}
    if "precisionTime" in t or "time" in t:
        return {"literal": {"precisionTime": {"precision": 6, "value": str(v)}}}
    if "fp64" in t or "fp32" in t:
        return literal(decode_double(v))
    if "decimal" in t:
        d = t["decimal"]
        value = base64.b64encode(v.to_bytes(16, "little", signed=True)).decode()
        return {
            "literal": {
                "decimal": {
                    "value": value,
                    "precision": d.get("precision", 38),
                    "scale": d.get("scale", 0),
                }
            }
        }
    return literal(v)


def inline_tables(plan: dict, rows: Mapping[str, list[tuple]]) -> dict:
    """Replace the reads of the tables in `rows` by virtual tables (in place)."""

    def walk(node: object) -> None:
        if isinstance(node, dict):
            if "namedTable" in node:
                name = ".".join(node.pop("namedTable")["names"])
                # A decimal takes its column's type (`baseSchema`).
                types = node.get("baseSchema", {}).get("struct", {}).get("types", [])
                decs = [t.get("decimal") if isinstance(t, dict) else None for t in types]

                def cell(i: int, v: object) -> dict:
                    d = decs[i] if i < len(decs) else None
                    if isinstance(v, Decimal) and d is not None:
                        return decimal_literal(v, d.get("precision", 38), d.get("scale", 0))
                    t = types[i] if i < len(types) and isinstance(types[i], dict) else {}
                    if isinstance(v, int) and not isinstance(v, bool):
                        # A value given by its code takes its column's kind (#923).
                        return typed_code(t, v)
                    return literal(v)

                exprs = [{"fields": [cell(i, v) for i, v in enumerate(row)]} for row in rows[name]]
                node["virtualTable"] = {"expressions": exprs}
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    return plan


def with_tables(plan: object, rows: Mapping[str, list[tuple]]) -> object:
    """`plan` with the reads of the tables in `rows` replaced by virtual
    tables, as `inline_tables` does, as a new plan: one pass, where a copy
    of the plan (through JSON) and `inline_tables` took three. Lists and
    dicts are new; strings and numbers are shared with `plan`."""
    if isinstance(plan, dict):
        if "namedTable" not in plan:
            return {k: with_tables(v, rows) for k, v in plan.items()}
        out = {k: with_tables(v, rows) for k, v in plan.items() if k != "namedTable"}
        return inline_tables({**out, "namedTable": plan["namedTable"]}, rows)
    if isinstance(plan, list):
        return [with_tables(v, rows) for v in plan]
    return plan


def _checked(plan_json: str, flags: tuple[str, ...] = ()) -> str:
    code, out, err = run_checker(flags, plan_json)
    if code != 0:
        raise subprocess.CalledProcessError(code, "substrait-check", out, err)
    return out


def lean_rows(plan_json: str) -> list[tuple]:
    """The rows `Rel.eval` gives for a plan with only virtual tables, in
    Lean's order. Doubles, timestamps and dates come back as their integer
    codes (`core/Sverify/Core/Float.lean`); doubles are refused."""
    out = _checked(plan_json)
    return parse_rows(out)


def lean_values(plan_json: str, rows_only: bool = False) -> list[tuple]:
    """Like `lean_rows`, but reads doubles too, which Lean prints with six
    decimals and a `d` (so only approximately). `rows_only` asks the checker
    for the rows alone (`--rows`), without the plan's other facts."""
    out = _checked(plan_json, ("--rows",) if rows_only else ())
    return parse_rows(out, doubles=True)


def lean_choices(plan_json: str) -> list[list[tuple]] | None:
    """The rows `Rel.evalChoices` gives for a plan with only virtual tables:
    each cell `("v", value)`, `("any", [value, …])` (a pick that ties),
    `("concat", sep, [[str, …], …])` or `("collect", [[value, …], …])` (the
    tie classes of `STRING_AGG` or `collect`, each in any order). None where
    the data leaves a choice Lean does not list (ties in a window or at a
    `FETCH`). Doubles as `lean_values` reads them (D24, #679)."""

    code, out, err = run_checker(("--eval-choices",), plan_json)
    if code != 0:
        raise subprocess.CalledProcessError(code, "substrait-check", out, err)
    rows = json.loads(out)["rows"]
    if rows is None:
        return None

    def val(text: str) -> object:
        return _parse_row(f"({text})", doubles=True)[0]

    def cell(c: dict) -> tuple:
        if "v" in c:
            return ("v", val(c["v"]))
        if "any" in c:
            return ("any", [val(x) for x in c["any"]])
        if "concat" in c:
            k = c["concat"]
            return ("concat", k["sep"], [[val(x) for x in cls] for cls in k["classes"]])
        return ("collect", [[val(x) for x in cls] for cls in c["collect"]])

    return [[cell(c) for c in row] for row in rows]


def _equal(a: object, b: object) -> bool:
    return a == b


def _candidates(
    rows: Sequence[Sequence[object]], choices: Sequence[Sequence[tuple]]
) -> list[Sequence[int]] | None:
    """For each row, the choice rows that agree with it on the columns every
    choice row fixes to one value: the only ones `row_ok` can accept when
    values compare by `==`. None where a value is not hashable."""
    width = len(choices[0]) if choices else 0
    keyed = [k for k in range(width) if all(len(c) == width and c[k][0] == "v" for c in choices)]
    index: dict[tuple, list[int]] = {}
    try:
        for j, c in enumerate(choices):
            index.setdefault(tuple(c[k][1] for k in keyed), []).append(j)
        return [
            index.get(tuple(got[k] for k in keyed), []) if len(got) == width else [] for got in rows
        ]
    except TypeError:  # a list or another unhashable value
        return None


def allows_rows(
    rows: Sequence[Sequence[object]],
    choices: Sequence[Sequence[tuple]],
    same: Callable[[object, object], bool] = _equal,
) -> bool:
    """Whether `rows`, as a multiset, are one result `choices` allows
    (`lean_choices`): a one-to-one matching of rows to choice rows, each
    cell one of its values. `same` compares two values (doubles to some
    precision, for one). The matching is `Relation.Near`'s (`Lipschitz.lean`):
    rows that tie on the exact columns pair up whatever order their doubles
    sort in."""

    def seq_ok(got: Sequence[object], classes: Sequence[Sequence[object]]) -> bool:
        pos = 0
        for cls in classes:
            part = list(got[pos : pos + len(cls)])
            pos += len(cls)
            if len(part) != len(cls):
                return False
            left = list(cls)
            for g in part:
                i = next((i for i, c in enumerate(left) if same(g, c)), None)
                if i is None:
                    return False
                left.pop(i)
        return pos == len(got)

    def concat_ok(got: object, sep: str, classes: Sequence[Sequence[object]]) -> bool:
        if not isinstance(got, str):
            return got is None and not classes
        # The strings of each class in some order, joined by `sep`.
        pending = [list(map(str, cls)) for cls in classes if cls]

        def go(text: str, k: int, left: list[str], first: bool) -> bool:
            if not left:
                if k + 1 == len(pending):
                    return text == ""
                return go(text, k + 1, list(pending[k + 1]), first)
            for i, piece in enumerate(left):
                head = piece if first else sep + piece
                if text.startswith(head) and go(
                    text[len(head) :], k, left[:i] + left[i + 1 :], False
                ):
                    return True
            return False

        return bool(pending) and go(got, 0, list(pending[0]), True)

    def cell_ok(got: object, c: tuple) -> bool:
        kind = c[0]
        if kind == "v":
            return same(got, c[1])
        if kind == "any":
            return any(same(got, v) for v in c[1])
        if kind == "concat":
            return concat_ok(got, c[1], c[2])
        return isinstance(got, list | tuple) and seq_ok(list(got), c[1])

    def row_ok(got: Sequence[object], want: Sequence[tuple]) -> bool:
        return len(got) == len(want) and all(cell_ok(g, w) for g, w in zip(got, want, strict=True))

    if len(rows) != len(choices):
        return False
    # A bipartite matching of rows to choice rows (Kuhn's augmenting paths),
    # over the choice rows that agree on the fixed columns where `==` decides.
    cands = _candidates(rows, choices) if same is _equal else None
    every = range(len(choices))
    edges = [
        [j for j in (cands[i] if cands is not None else every) if row_ok(got, choices[j])]
        for i, got in enumerate(rows)
    ]
    owner: list[int | None] = [None] * len(choices)

    def augment(i: int, seen: set[int]) -> bool:
        for j in edges[i]:
            if j in seen:
                continue
            seen.add(j)
            o = owner[j]
            if o is None or augment(o, seen):
                owner[j] = i
                return True
        return False

    return all(augment(i, set()) for i in range(len(rows)))


_TOKEN = re.compile(r'\s*(NULL|true|false|"(?:[^"\\]|\\.)*"|\[|\]|,|[^,\[\]]+)')
_ESCAPE = re.compile(r"\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)")


def _unquote(s: str) -> str:
    """A string in Lean's quotes (`String.quote`, which escapes with `\\x..`)."""

    def char(m: re.Match[str]) -> str:
        e = m.group(1)
        if e[0] == "x":
            return chr(int(e[1:], 16))
        if e[0] == "u":
            return chr(int(e[2:-1], 16))
        return {"n": "\n", "t": "\t", "r": "\r"}.get(e, e)

    return _ESCAPE.sub(char, s[1:-1])


def _value(x: str, doubles: bool) -> object:
    if x == "NULL":
        return None
    if x in ("true", "false"):
        return x == "true"
    if x.startswith('"'):
        return _unquote(x)
    if re.fullmatch(r"-?\d+", x):
        return int(x)
    # A decimal, as `Main.decimalString` prints it.
    if re.fullmatch(r"-?\d+\.\d+", x):
        return Decimal(x)
    if doubles and x.endswith("d"):
        return float(x[:-1])
    raise ValueError(f"cannot read {x!r} (a double?) from Lean's output")


def _parse_row(text: str, doubles: bool = False) -> tuple:
    """One row as `Row.render` prints it: `(v, …)`, lists as `[v, …]`."""
    tokens = [m.group(1) for m in _TOKEN.finditer(text.strip()[1:-1])]
    pos = 0

    def items(close: str | None) -> list[object]:
        nonlocal pos
        out: list[object] = []
        while pos < len(tokens) and tokens[pos] != close:
            t = tokens[pos]
            pos += 1
            if t == ",":
                continue
            if t == "[":
                out.append(items("]"))
                pos += 1  # the "]"
            else:
                out.append(_value(t.strip(), doubles))
        return out

    return tuple(items(None))


def parse_rows(output: str, doubles: bool = False) -> list[tuple]:
    """The rows section of `substrait-check` output (`renderCell` in `Main.lean`)."""
    rows = []
    # Lines end at `\n` only: a string may hold U+0085 or U+2028, which
    # `str.splitlines` also breaks at.
    for line in output.split("rows (")[1].split("\n")[1:]:
        if not line.startswith("  ("):
            break
        rows.append(_parse_row(line, doubles))
    return rows

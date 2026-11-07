"""Reading Lean's written plans: the protobuf JSON that `substrait-check`
writes, decoded once for every backend that reads it (the SQL writer,
`sverify.sql.core`, and the Polars engine).

Internal: not part of sverify's public API. `sverify.plan_json` is the other
direction, the producers' encoding.

The decoders return neutral values (a kind and a payload); each backend maps
them to its own types. Every decoder raises `err`, the caller's
`Unsupported`, on what it does not read.
"""

from __future__ import annotations

import base64
import json
import math
import re
from typing import Any

#: `Text.substrMax`: `substring`'s offsets lie in `[-SUBSTR_MAX, SUBSTR_MAX)`,
#: its lengths below `SUBSTR_MAX` (#336).
SUBSTR_MAX = 2**32
#: `Text.repeatMax`: the longest string DataFusion's `repeat` writes, in bytes.
REPEAT_MAX = 2**31 - 1
US_PER_DAY = 86_400_000_000

Err = type[Exception]

_INTS = ("i8", "i16", "i32", "i64")


def short(j: Any) -> str:
    s = json.dumps(j, separators=(",", ":"))
    return s if len(s) <= 80 else s[:80] + "…"


def integer(j: Any, err: Err = ValueError) -> int:
    """An integer, as a JSON number or a string of digits (64-bit values)."""
    if isinstance(j, int) and not isinstance(j, bool):
        return j
    if isinstance(j, str) and re.fullmatch(r"-?\d+", j):
        return int(j)
    raise err(f"expected integer, got {j!r}")


def natural(j: dict, k: str, err: Err = ValueError) -> int:
    """The non-negative integer member `k`, 0 if absent."""
    v = j.get(k) if isinstance(j, dict) else None
    i = 0 if v is None else integer(v, err)
    if i < 0:
        raise err(f"expected non-negative integer, got {i}")
    return i


def base_name(name: str) -> str:
    """A function's name without its signature (`add:i64_i64` → `add`)."""
    return name.split(":")[0]


def function_names(plan: Any, err: Err = ValueError) -> dict[int, str]:
    """The plan's function anchors and their full names; the first
    declaration of an anchor wins."""
    fns: dict[int, str] = {}
    exts = plan.get("extensions") if isinstance(plan, dict) else None
    if exts is None:
        return fns
    if not isinstance(exts, list):
        raise err("expected an array in 'extensions'")
    for e in exts:
        f = e.get("extensionFunction") if isinstance(e, dict) else None
        if f is None:
            continue
        name = f.get("name") if isinstance(f, dict) else None
        if name is None:
            raise err(f"missing field 'name' in {short(f)}")
        fns.setdefault(natural(f, "functionAnchor", err), name)
    return fns


# --- Types ------------------------------------------------------------------


def type_kind(t: Any) -> tuple[str, Any] | None:
    """A Substrait type as a kind and its payload, `None` for one Lean does
    not write:

    `int` (its key), `float` (its key), `str`, `bool`, `date`, `interval`,
    `time` and `tod` (their precision, `None` if malformed), `decimal`
    (precision and scale), `list` (the element type) and `struct` (the field
    types)."""
    if not isinstance(t, dict):
        return None
    if key := next((k for k in _INTS if k in t), None):
        return "int", key
    if key := next((k for k in ("fp32", "fp64") if k in t), None):
        return "float", key
    if "timestamp" in t:
        return "time", 6
    if "precisionTimestamp" in t:
        return "time", _precision(t["precisionTimestamp"])
    if "date" in t:
        return "date", None
    if "time" in t:
        return "tod", 6
    if "precisionTime" in t:
        return "tod", _precision(t["precisionTime"])
    if any(k in t for k in ("string", "varchar", "fixedChar")):
        return "str", None
    if "bool" in t:
        return "bool", None
    if "intervalDayToSecond" in t:
        return "interval", None
    # A scale of 0 is left out of the JSON (`typeKind`).
    if isinstance(d := t.get("decimal"), dict):
        return "decimal", (d.get("precision", 38), d.get("scale", 0))
    if isinstance(lt := t.get("list"), dict):
        return "list", lt.get("type")
    if isinstance(st := t.get("struct"), dict):
        return "struct", st.get("types", [])
    return None


def _precision(body: Any) -> int | None:
    return body.get("precision", 0) if isinstance(body, dict) else None


# --- Literals ---------------------------------------------------------------

_LITERAL_KEYS = (
    "boolean", *_INTS, "fp32", "fp64", "string", "null", "decimal",
    "precisionTimestamp", "timestamp", "date", "precisionTime", "time", "intervalDayToSecond",
    "intervalYearToMonth", "intervalCompound", "list", "struct", "emptyList",
)  # fmt: skip


def parse_double(s: str) -> float | None:
    """A double written as a string: `NaN`, `Infinity` and `-Infinity` as
    Lean writes them (case and a `+` aside), or a JSON number."""
    t = s.strip().lower()
    if t in ("inf", "+inf", "infinity", "+infinity"):
        return math.inf
    if t in ("-inf", "-infinity"):
        return -math.inf
    if t == "nan":
        return math.nan
    try:
        n = json.loads(t)
    except ValueError:
        return None
    return float(n) if isinstance(n, int | float) and not isinstance(n, bool) else None


def literal(lit: Any, err: Err = ValueError) -> tuple[str, Any]:
    """A literal as a kind and its value:

    `bool`, `str`, `float`, `int` (its key and value), `null` (its type),
    `decimal` (unscaled value, precision, scale), `time` and `tod`
    (microseconds), `date` (days), `interval` (months and microseconds),
    `list` and `struct` (their literals) and `emptyList` (its type)."""
    key = next((k for k in _LITERAL_KEYS if isinstance(lit, dict) and lit.get(k) is not None), None)
    if key is None:
        raise err(f"unsupported literal: {short(lit)}")
    v = lit[key]
    match key:
        case "boolean":
            if not isinstance(v, bool):
                raise err("malformed boolean literal")
            return "bool", v
        case "string":
            if not isinstance(v, str):
                raise err("malformed string literal")
            return "str", v
        case "fp32" | "fp64":
            f = (
                float(v)
                if isinstance(v, int | float) and not isinstance(v, bool)
                else parse_double(v)
                if isinstance(v, str)
                else None
            )
            if f is None:
                raise err(f"malformed floating-point literal {v!r}")
            return "float", f
        case "null" | "emptyList":
            return key, v.get("type", {"i64": {}}) if key == "emptyList" else v
        case "decimal":
            p, s = natural(v, "precision", err), natural(v, "scale", err)
            return "decimal", (_decimal(_req(v, "value", err), err), p, s)
        case "intervalDayToSecond":
            return "interval", (0, interval_micros(v, err))
        case "intervalYearToMonth":
            return "interval", (year_months(v, err), 0)
        case "intervalCompound":
            ym, ds = v.get("intervalYearToMonth"), v.get("intervalDayToSecond")
            months = 0 if ym is None else year_months(ym, err)
            return "interval", (months, 0 if ds is None else interval_micros(ds, err))
        case "precisionTimestamp":
            if natural(v, "precision", err) != 6:
                raise err("only microsecond timestamps are supported")
            return "time", integer(_req(v, "value", err), err)
        case "timestamp":
            return "time", integer(v, err)
        case "date":
            return "date", integer(v, err)
        case "precisionTime":
            p, value = natural(v, "precision", err), integer(_req(v, "value", err), err)
            if p <= 6:
                return "tod", value * 10 ** (6 - p)
            if value % 10 ** (p - 6):
                raise err("times finer than microseconds are not supported")
            return "tod", value // 10 ** (p - 6)
        case "time":
            return "tod", integer(v, err)
        case "list":
            return "list", v.get("values", [])
        case "struct":
            return "struct", v.get("fields", [])
    return "int", (key, integer(v, err))


def _req(j: dict, k: str, err: Err) -> Any:
    v = j.get(k) if isinstance(j, dict) else None
    if v is None:
        raise err(f"missing field '{k}' in {short(j)}")
    return v


def _decimal(s: str, err: Err) -> int:
    try:
        raw = base64.b64decode(s, validate=False)
    except ValueError as e:
        raise err("malformed decimal literal") from e
    return int.from_bytes(raw, "little", signed=True) if raw else 0


def interval_micros(d: dict, err: Err = ValueError) -> int:
    """`intervalDayToSecond` in microseconds (`Parse.intervalMicros`)."""
    days = integer(d.get("days") or 0, err)
    secs = integer(d.get("seconds") or 0, err)
    sub = integer(d.get("subseconds") or 0, err)
    p = natural(d, "precision", err)
    # Lean's `Int` division rounds toward negative infinity here (`Int.div` is
    # `ediv` for a positive divisor), like Python's `//`.
    sub_us = sub // 10 ** (p - 6) if p >= 6 else sub * 10 ** (6 - p)
    return (days * 86400 + secs) * 1_000_000 + sub_us


def year_months(ym: dict, err: Err = ValueError) -> int:
    """`intervalYearToMonth` in months."""
    return 12 * integer(ym.get("years") or 0, err) + integer(ym.get("months") or 0, err)


# --- Regular expressions ----------------------------------------------------


_PLAIN_NOT = set("\\.+*?()|[]{}^$")
_ESCAPABLE = set("\\.+*?()|[]{}^$-dDwWsSnt")
_NOT_IN_CLASS = set("[]\\-&~^")


def simple_regex(p: str) -> bool:
    """`Text.simpleRegex`: is `p` in the subset of patterns that compile in
    RE2 and Rust and that `SubstraitLean/Regex.lean` evaluates?"""

    def count(cs: str) -> tuple[int, str] | None:
        ds = cs[: len(cs) - len(cs.lstrip("0123456789"))]
        if not ds or len(ds) > 4 or int(ds) > 1000:
            return None
        return int(ds), cs[len(ds) :]

    def quantifier(cs: str) -> str | None:
        if cs[:1] in ("*", "+", "?") and cs:
            return cs[1:]
        if cs[:1] != "{":
            return cs
        c = count(cs[1:])
        if c is None:
            return None
        n, r = c
        if r[:1] == "}":
            return r[1:]
        if r[:2] == ",}":
            return r[2:]
        if r[:1] == ",":
            c2 = count(r[1:])
            if c2 is None:
                return None
            m, r = c2
            return r[1:] if r[:1] == "}" and n <= m else None
        return None

    def class_items(fuel: int, cs: str) -> str | None:
        while fuel > 0:
            fuel -= 1
            if not cs:
                return None
            if cs[0] == "]":
                return cs[1:]
            if cs[0] == "\\" and len(cs) > 1:
                if cs[1] not in "dDwWsS\\[]-^":
                    return None
                cs = cs[2:]
            elif len(cs) > 2 and cs[1] == "-":
                a, b = cs[0], cs[2]
                if not (a not in _NOT_IN_CLASS and b not in _NOT_IN_CLASS and a <= b):
                    return None
                cs = cs[3:]
            elif cs[0] not in _NOT_IN_CLASS:
                cs = cs[1:]
            else:
                return None
        return None

    def class_body(cs: str) -> str | None:
        if cs[:1] == "^":
            cs = cs[1:]
        if cs[:1] == "]":
            return None
        return class_items(len(cs) + 1, cs)

    def alternatives(fuel: int, cs: str) -> str | None:
        while fuel > 0:
            fuel -= 1
            r = sequence(fuel, cs)
            if r is None:
                return None
            if r[:1] != "|":
                return r
            cs = r[1:]
        return None

    def sequence(fuel: int, cs: str) -> str | None:
        while fuel > 0:
            fuel -= 1
            if not cs:
                return ""
            c = cs[0]
            if c in ")|":
                return cs
            if c in "^$":
                r: str | None = cs[1:]
            elif c == "\\" and len(cs) > 1:
                if cs[1] in "bB":
                    r = cs[2:]
                elif cs[1] in _ESCAPABLE:
                    r = quantifier(cs[2:])
                else:
                    return None
            elif c == ".":
                r = quantifier(cs[1:])
            elif c == "(":
                body = cs[3:] if cs[1:3] == "?:" else cs[1:]
                inner = alternatives(fuel, body)
                if inner is None or inner[:1] != ")":
                    return None
                r = quantifier(inner[1:])
            elif c == "[":
                b = class_body(cs[1:])
                r = None if b is None else quantifier(b)
            elif c not in _PLAIN_NOT:
                r = quantifier(cs[1:])
            else:
                return None
            if r is None:
                return None
            cs = r
        return None

    return len(p) <= 200 and alternatives(3 * len(p) + 3, p) == ""


def regex_groups(p: str, err: Err = ValueError) -> int:
    """The entries `regexp_match(s, p)` has on a match: its capture groups, or
    the whole match if there are none (`Text.regexGroups`). Groups are counted
    as `(` outside classes and escapes, but `(?:`; any other `(?` is refused,
    as `Text.simpleRegex` does."""
    groups, k, in_class = 0, 0, False
    while k < len(p):
        c = p[k]
        if c == "\\":
            k += 2
            continue
        if in_class:
            in_class = c != "]"
        elif c == "[":
            in_class = True
            # A `]` right after `[` or `[^` is a literal member.
            if p[k + 1 : k + 2] == "^":
                k += 1
            if p[k + 1 : k + 2] == "]":
                k += 1
        elif c == "(":
            if p[k + 1 : k + 3] == "?:":
                # Non-capturing.
                k += 1
            elif p[k + 1 : k + 2] == "?":
                raise err(f"regular expressions with '(?' are not supported: {p!r}")
            else:
                groups += 1
        k += 1
    return max(groups, 1)

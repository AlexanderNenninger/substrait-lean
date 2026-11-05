"""The lift's rules of strings: functions of strings, LIKE and ILIKE, `||`."""

from __future__ import annotations

from collections.abc import Callable
from typing import Any

import ibis.expr.datatypes as dt
import sqlglot.expressions as sge

from sverify import _functions
from sverify.plan_json import (
    Json,
    Unsupported,
    call,
    chain,
    if_then,
    literal,
    substring_left,
)
from sverify.sql_lift._base import Column, E, Sub, _fn, _Lift, _option, _shown, register

# -- strings ---------------------------------------------------------------


def _strings(lf: _Lift, es: list[E], what: str) -> list[Json]:
    """Arguments that must be strings (a NULL is a string NULL)."""
    for e in es:
        if not (e.type.is_string() or e.type.is_null()):
            raise Unsupported(f"{what} of a {e.type} is not supported yet")
    return [lf.to(e, dt.string).json for e in es]


_TYPES = {"str": dt.string, "int": dt.int64, "bool": dt.boolean}


def _string_fn(f: _functions.Fn) -> Callable[..., E]:
    """A function of strings of the function table: `upper(s)`, `s || t`,
    `starts_with(s, t)`, …"""
    out = _TYPES[f.result]

    def rule(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
        args = [node.this, *(a for a in [node.args.get("expression")] if a is not None)]
        return E(_fn(f.name, _strings(lf, [sub(a) for a in args], f.what), out), out)

    return rule


def _reverse(lf: _Lift, node: sge.Reverse, sub: Sub, scope: list[Column]) -> E:
    raise Unsupported(
        "reverse is not supported yet: DuckDB reverses grapheme clusters, the model code points"
    )


def _length(lf: _Lift, node: sge.Length, sub: Sub, scope: list[Column]) -> E:
    # Characters (code points), a BIGINT; `strlen` (bytes) is another node.
    if node.args.get("binary"):
        raise Unsupported("the length of a BLOB is not supported")
    (s_,) = _strings(lf, [sub(node.this)], "length")
    return E(_fn("character_length", [s_], dt.int64), dt.int64)


def _trim(lf: _Lift, node: sge.Trim, sub: Sub, scope: list[Column]) -> E:
    # DuckDB trims spaces, or the characters given.
    position = (node.args.get("position") or "BOTH").upper()
    name = {"BOTH": "btrim", "LEADING": "ltrim", "TRAILING": "rtrim"}.get(position)
    if name is None or node.args.get("collation"):
        raise Unsupported(f"{_shown(node)} is not supported yet")
    chars = node.args.get("expression")
    s_, c = _strings(
        lf, [sub(node.this), sub(chars) if chars is not None else _const_str(" ")], name
    )
    return E(_fn(name, [s_, c], dt.string), dt.string)


def _const_str(v: str) -> E:
    return E(literal(v, dt.string), dt.string, v)


def _substring(lf: _Lift, node: sge.Substring, sub: Sub, scope: list[Column]) -> E:
    # DuckDB counts from 1, and from the end for a negative start: Substrait's
    # `negative_start` WRAP_FROM_END, the reference's default (#209 R13).
    s_ = sub(node.this)
    start, length = node.args.get("start"), node.args.get("length")
    args = _strings(lf, [s_], "substring")
    for a in (start, length):
        if a is None:
            continue
        e = sub(a)
        if not (e.type.is_integer() or e.type.is_null()):
            raise Unsupported(f"substring with a {e.type} position is not supported")
        if a is length and e.constant and e.value is not None and e.value < 0:
            raise Unsupported("substring with a negative length is not supported yet")
        args.append(lf.to(e, dt.int64).json)
    if start is None:
        raise Unsupported("substring needs a start")
    opt = _option("negative_start", "WRAP_FROM_END")
    return E(_fn("substring", args, dt.string, [opt]), dt.string)


def _strpos(lf: _Lift, node: sge.StrPosition, sub: Sub, scope: list[Column]) -> E:
    # 1-based, 0 if absent; `strpos(s, '')` is 1.
    if node.args.get("position") is not None or node.args.get("occurrence") is not None:
        raise Unsupported(f"{_shown(node)} is not supported yet")
    args = _strings(lf, [sub(node.this), sub(node.args["substr"])], "strpos")
    return E(_fn("strpos", args, dt.int64), dt.int64)


def _contains(lf: _Lift, node: sge.Contains, sub: Sub, scope: list[Column]) -> E:
    s_, t = _strings(lf, [sub(node.this), sub(node.expression)], "contains")
    pos = _fn("strpos", [s_, t], dt.int64)
    return E(_fn("gt", [pos, literal(0, dt.int64)], dt.boolean), dt.boolean)


def _like(name: str) -> Callable[..., E]:
    def rule(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
        # DuckDB's LIKE has no escape character without ESCAPE: a backslash
        # is itself. The model's (DataFusion's) escapes with a backslash, so
        # a pattern must be a constant without one.
        p = sub(node.expression)
        if not p.constant:
            raise Unsupported(f"{name.upper()} with a pattern that is not a constant")
        if isinstance(p.value, str) and "\\" in p.value:
            raise Unsupported(
                f"{name.upper()} with a backslash in the pattern is not supported yet"
            )
        args = _strings(lf, [sub(node.this), p], name)
        return E(_fn(name, args, dt.boolean), dt.boolean)

    return rule


def _concat(lf: _Lift, node: sge.Concat, sub: Sub, scope: list[Column]) -> E:
    # `concat(…)` leaves out NULLs: '' for all of them. A constant string is
    # never NULL, so it needs no `coalesce`, and constants next to each other
    # are one literal.
    es = [sub(a) for a in node.expressions]
    args = _strings(lf, es, "concat")
    empty = literal("", dt.string)
    parts: list[Json] = []
    text: str | None = None  # the constants since the last column
    for e, a in zip(es, args, strict=True):
        if e.constant:
            text = (text or "") + (e.value or "")
            continue
        if text:
            parts.append(literal(text, dt.string))
        text = None
        parts.append(_fn("coalesce", [a, empty], dt.string))
    if text or not parts:
        parts.append(literal(text or "", dt.string))
    if len(parts) == 1 and all(e.constant for e in es):
        return E(parts[0], dt.string, text or "")
    return E(chain("str_concat", parts), dt.string)


def _replace(lf: _Lift, node: sge.Replace, sub: Sub, scope: list[Column]) -> E:
    pattern, replacement = sub(node.expression), sub(node.args["replacement"])
    if not (pattern.constant and replacement.constant):
        raise Unsupported("replace needs a constant pattern and replacement")
    args = _strings(lf, [sub(node.this), pattern, replacement], "replace")
    return E(_fn("replace", args, dt.string), dt.string)


def _repeat(lf: _Lift, node: sge.Repeat, sub: Sub, scope: list[Column]) -> E:
    n = sub(node.args["times"])
    if not (n.type.is_integer() or n.type.is_null()):
        raise Unsupported(f"repeat by a {n.type} is not supported")
    (s_,) = _strings(lf, [sub(node.this)], "repeat")
    return E(_fn("repeat", [s_, lf.to(n, dt.int64).json], dt.string), dt.string)


def _left(lf: _Lift, node: sge.Left, sub: Sub, scope: list[Column]) -> E:
    # The first `n` characters; a negative `n` is not supported.
    n = sub(node.expression)
    if not (n.constant and isinstance(n.value, int) and n.value >= 0):
        raise Unsupported("left needs a constant count of 0 or more")
    (s_,) = _strings(lf, [sub(node.this)], "left")
    args = [s_, literal(1, dt.int64), literal(n.value, dt.int64)]
    return E(_fn("substring", args, dt.string), dt.string)


def _affix(name: str) -> Callable[[_Lift, list[E]], E]:
    """`prefix(s, t)`, `suffix(s, t)` (DuckDB's names)."""

    def rule(lf: _Lift, args: list[E]) -> E:
        return E(_fn(name, _strings(lf, args, name), dt.boolean), dt.boolean)

    return rule


def _sha2(lf: _Lift, node: sge.SHA2, sub: Sub, scope: list[Column]) -> E:
    # DuckDB's `sha256(s)`, which SQLGlot reads as `SHA2(s, 256)`.
    n = node.args.get("length")
    if not (isinstance(n, sge.Literal) and n.this == "256"):
        raise Unsupported("SHA2 of a length other than 256 is not supported")
    (s_,) = _strings(lf, [sub(node.this)], "sha256")
    return E(_fn("sha256", [s_], dt.string), dt.string)


# -- regular expressions, padding, splitting (#808) ---------------------------


def _const(e: E, what: str, kind: type) -> Any:
    """The value of a constant argument of type `kind` (None for NULL)."""
    if not e.constant or not (e.value is None or isinstance(e.value, kind)):
        raise Unsupported(f"{what} needs a constant {kind.__name__}")
    if isinstance(e.value, bool):
        raise Unsupported(f"{what} needs a constant {kind.__name__}")
    return e.value


def _pattern(lf: _Lift, node: sge.Expression, sub: Sub, what: str) -> tuple[Json, str]:
    """The string and the constant pattern of a regular expression function."""
    p = sub(node.expression)
    if not (p.constant and isinstance(p.value, str)):
        raise Unsupported(f"{what} needs a constant pattern")
    (s_,) = _strings(lf, [sub(node.this)], what)
    return s_, p.value


def _null(t: Any) -> E:
    return E(literal(None, t), t, None)


def _regexp_like(full: bool) -> Callable[..., E]:
    """`regexp_matches(s, p)`: does `p` match somewhere in `s`;
    `regexp_full_match(s, p)`: all of it. NULL for a NULL `s`."""
    what = "regexp_full_match" if full else "regexp_matches"

    def rule(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
        if node.args.get("flag") is not None or node.args.get("options") is not None:
            raise Unsupported(f"{what} with options is not supported yet")
        s_, p = _pattern(lf, node, sub, what)
        if full:
            # RE2's `$` is the end of the text, without the `m` flag.
            p = f"^(?:{p})$"
        matches = call("array_length", [call("regexp_match", [s_, literal(p, dt.string)])])
        found = call("gt", [matches, literal(0, dt.int64)])
        found = call("coalesce", [found, literal(False, dt.boolean)])
        null = literal(None, dt.boolean)
        return E(if_then([(call("is_null", [s_]), null)], found), dt.boolean)

    return rule


def _regexp_extract(lf: _Lift, node: sge.RegexpExtract, sub: Sub, scope: list[Column]) -> E:
    # Group `g` of the first match, `''` without one (or past the groups).
    if node.args.get("position") is not None or node.args.get("occurrence") is not None:
        raise Unsupported(f"{_shown(node)} is not supported yet")
    if node.args.get("parameters") is not None:
        raise Unsupported("regexp_extract with options is not supported yet")
    s_, p = _pattern(lf, node, sub, "regexp_extract")
    group = node.args.get("group")
    g = 0 if group is None else _const(sub(group), "regexp_extract's group", int)
    if g is None or g < 0:
        raise Unsupported("regexp_extract needs a group number of at least 0")
    args = [s_, literal(p, dt.string), literal(g, dt.int64)]
    return E(call("regexp_extract", args), dt.string)


def _regexp_replace(lf: _Lift, node: sge.RegexpReplace, sub: Sub, scope: list[Column]) -> E:
    # The first match, or every match with the flag `'g'`.
    for k in ("position", "occurrence"):
        if node.args.get(k) is not None:
            raise Unsupported(f"{_shown(node)} is not supported yet")
    flags = node.args.get("modifiers")
    flag = None if flags is None else _const(sub(flags), "regexp_replace's options", str)
    if flag not in (None, "g"):
        raise Unsupported(f"regexp_replace with the options {flag!r} is not supported (only 'g')")
    s_, p = _pattern(lf, node, sub, "regexp_replace")
    r = sub(node.args["replacement"])
    if not (r.constant and isinstance(r.value, str)):
        raise Unsupported("regexp_replace needs a constant replacement")
    args = [s_, literal(p, dt.string), literal(r.value, dt.string)]
    if flag == "g":
        args.append(literal("g", dt.string))
    return E(call("regexp_replace", args), dt.string)


def _right(lf: _Lift, node: sge.Right, sub: Sub, scope: list[Column]) -> E:
    # The last `n` characters, or all but the first `-n` for a negative `n`.
    n = _const(sub(node.expression), "right", int)
    (s_,) = _strings(lf, [sub(node.this)], "right")
    if n is None:
        return _null(dt.string)
    if n < 0:
        return E(_fn("substring", [s_, literal(1 - n, dt.int64)], dt.string), dt.string)
    size = call("character_length", [s_])
    start = call("add", [call("subtract", [size, literal(n, dt.int64)]), literal(1, dt.int64)])
    return E(substring_left([s_, start]), dt.string)


def _pad(lf: _Lift, node: sge.Pad, sub: Sub, scope: list[Column]) -> E:
    """`lpad(s, n, p)`, `rpad(s, n, p)`: the first `n` characters of `s`, or
    `s` filled to `n` characters with `p` repeated and cut, as DuckDB pads.
    For a constant `n` and `p`; DuckDB raises for `p = ''` where `s` is
    shorter than `n`."""
    left = bool(node.args.get("is_left"))
    what = "lpad" if left else "rpad"
    fill = node.args.get("fill_pattern")
    if fill is None:
        raise Unsupported(f"{what} needs a fill")
    n = _const(sub(node.expression), what, int)
    p = _const(sub(fill), f"{what}'s fill", str)
    (s_,) = _strings(lf, [sub(node.this)], what)
    if n is None or p is None:
        return _null(dt.string)
    if n <= 0:
        return E(if_then([(call("is_null", [s_]), literal(None, dt.string))],
                         literal("", dt.string)), dt.string)  # fmt: skip
    if p == "":
        raise Unsupported(f"{what} with an empty fill: DuckDB raises where the string is shorter")
    size = call("character_length", [s_])
    cut = call("substring", [s_, literal(1, dt.int64), literal(n, dt.int64)])
    # The fill is the first `n - size` characters of `p` repeated: those of
    # a constant from the left of its beginning.
    filler = literal((p * n)[:n], dt.string)
    start = call("subtract", [literal(1, dt.int64), size])
    part = substring_left([filler, start, literal(n, dt.int64)])
    padded = call("str_concat", [part, s_] if left else [s_, part])
    return E(if_then([(call("gte", [size, literal(n, dt.int64)]), cut)], padded), dt.string)


def _concat_ws(lf: _Lift, node: sge.ConcatWs, sub: Sub, scope: list[Column]) -> E:
    """`concat_ws(sep, …)`: the arguments that are not NULL, joined by `sep`;
    `''` if all are NULL, NULL if `sep` is. Each is `sep || a`, or `''` for a
    NULL `a`; the first `sep` is dropped."""
    sep, *rest = _strings(lf, [sub(a) for a in node.expressions], "concat_ws")
    if not rest:
        raise Unsupported("concat_ws needs a value to join")
    empty = literal("", dt.string)
    parts = [call("coalesce", [call("str_concat", [sep, a]), empty]) for a in rest]
    start = call("add", [call("character_length", [sep]), literal(1, dt.int64)])
    return E(call("substring", [chain("str_concat", parts), start]), dt.string)


def _split_part(lf: _Lift, node: sge.SplitPart, sub: Sub, scope: list[Column]) -> E:
    """`split_part(s, sep, n)`: the `n`-th piece of `string_split(s, sep)`
    (a black box), from 1, from the end for a negative `n`, `''` past the
    pieces and for `n = 0`; NULL if `s` or `sep` is."""
    n = _const(sub(node.args["part_index"]), "split_part's index", int)
    s_e, sep_e = sub(node.this), sub(node.args["delimiter"])
    s_, sep = _strings(lf, [s_e, sep_e], "split_part")
    if n is None:
        return _null(dt.string)
    pieces = _fn("string_split", [s_, sep], dt.Array(value_type=dt.string))
    empty = literal("", dt.string)
    if n == 0:
        piece = empty
    else:
        ref = {"listElement": {"offset": n - 1 if n > 0 else n}}
        elem = {"selection": {"directReference": ref, "expression": pieces}}
        piece = call("coalesce", [elem, empty])
    nulls = [
        (call("is_null", [j]), literal(None, dt.string))
        for e, j in ((s_e, s_), (sep_e, sep))
        if not (e.constant and e.value is not None)
    ]
    return E(if_then(nulls, piece) if nulls else piece, dt.string)


_ANONYMOUS_STRINGS = {"prefix": _affix("starts_with"), "suffix": _affix("ends_with")}


register(
    {
        # The function table's: `upper`, `lower`, `||`, `starts_with`, `ends_with`,
        # `md5`.
        **{getattr(sge, n): _string_fn(f) for f in _functions.area("strings") for n in f.lift},
        sge.Length: _length,
        sge.Reverse: _reverse,
        sge.Trim: _trim,
        sge.Substring: _substring,
        sge.StrPosition: _strpos,
        sge.Contains: _contains,
        sge.Like: _like("like"),
        sge.ILike: _like("ilike"),
        sge.Concat: _concat,
        sge.Replace: _replace,
        sge.Repeat: _repeat,
        sge.Left: _left,
        sge.SHA2: _sha2,
        sge.RegexpLike: _regexp_like(full=False),
        sge.RegexpFullMatch: _regexp_like(full=True),
        sge.RegexpExtract: _regexp_extract,
        sge.RegexpReplace: _regexp_replace,
        sge.Right: _right,
        sge.Pad: _pad,
        sge.ConcatWs: _concat_ws,
        sge.SplitPart: _split_part,
    }
)

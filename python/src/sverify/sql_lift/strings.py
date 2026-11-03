"""The lift's rules of strings: functions of strings, LIKE and ILIKE, `||`."""

from __future__ import annotations

from collections.abc import Callable
from typing import Any

import ibis.expr.datatypes as dt
import sqlglot.expressions as sge

from sverify.plan_json import Json, Unsupported, chain, literal
from sverify.sql_lift._base import Column, E, Sub, _fn, _Lift, _option, _shown, register

# -- strings ---------------------------------------------------------------


def _strings(lf: _Lift, es: list[E], what: str) -> list[Json]:
    """Arguments that must be strings (a NULL is a string NULL)."""
    for e in es:
        if not (e.type.is_string() or e.type.is_null()):
            raise Unsupported(f"{what} of a {e.type} is not supported yet")
    return [lf.to(e, dt.string).json for e in es]


def _string_fn(name: str, out: Any = dt.string) -> Callable[..., E]:
    """A function of strings: `upper(s)`, `reverse(s)`, `starts_with(s, t)`, …"""

    def rule(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
        args = [node.this, *(a for a in [node.args.get("expression")] if a is not None)]
        return E(_fn(name, _strings(lf, [sub(a) for a in args], name), out), out)

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


def _dpipe(lf: _Lift, node: sge.DPipe, sub: Sub, scope: list[Column]) -> E:
    # `a || b` is NULL if either is.
    args = _strings(lf, [sub(node.this), sub(node.expression)], "||")
    return E(_fn("str_concat", args, dt.string), dt.string)


def _concat(lf: _Lift, node: sge.Concat, sub: Sub, scope: list[Column]) -> E:
    # `concat(…)` leaves out NULLs: '' for all of them.
    args = _strings(lf, [sub(a) for a in node.expressions], "concat")
    empty = literal("", dt.string)
    parts = [_fn("coalesce", [a, empty], dt.string) for a in args]
    return E(chain("str_concat", parts) if parts else empty, dt.string)


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


_ANONYMOUS_STRINGS = {"prefix": _affix("starts_with"), "suffix": _affix("ends_with")}


register(
    {
        sge.Length: _length,
        sge.Upper: _string_fn("upper"),
        sge.Lower: _string_fn("lower"),
        sge.Reverse: _reverse,
        sge.StartsWith: _string_fn("starts_with", dt.boolean),
        sge.EndsWith: _string_fn("ends_with", dt.boolean),
        sge.Trim: _trim,
        sge.Substring: _substring,
        sge.StrPosition: _strpos,
        sge.Contains: _contains,
        sge.Like: _like("like"),
        sge.ILike: _like("ilike"),
        sge.DPipe: _dpipe,
        sge.Concat: _concat,
        sge.Replace: _replace,
        sge.Repeat: _repeat,
        sge.Left: _left,
    }
)

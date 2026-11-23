"""The lift's rules of strings: functions of strings, LIKE and ILIKE, `||`."""

from __future__ import annotations

from collections.abc import Callable
from typing import Any

import ibis.expr.datatypes as dt
import sqlglot.expressions as sge

from sverify import _functions
from sverify._plan_read import simple_regex
from sverify.plan_json import (
    Json,
    SqlUnsupported,
    Unsupported,
    call,
    chain,
    if_then,
    literal,
    logical,
    substring_left,
)
from sverify.sql_lift._base import (
    CONSTANT_FIX,
    Column,
    E,
    Sub,
    _fn,
    _Lift,
    _option,
    _shown,
    register,
)

# -- strings ---------------------------------------------------------------


def _strings(lf: _Lift, es: list[E], what: str) -> list[Json]:
    """Arguments that must be strings (a NULL is a string NULL)."""
    for e in es:
        if not (e.type.is_string() or e.type.is_null()):
            raise SqlUnsupported(
                f"{what} of a {e.type} is not supported yet", construct=f"function {what}"
            )
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
    raise SqlUnsupported(
        "reverse is not supported yet: DuckDB reverses grapheme clusters, the model code points",
        construct="function reverse",
    )


def _length(lf: _Lift, node: sge.Length, sub: Sub, scope: list[Column]) -> E:
    # Characters (code points), a BIGINT; `strlen` (bytes) is another node.
    if node.args.get("binary"):
        raise SqlUnsupported("the length of a BLOB is not supported", construct="function length")
    x = sub(node.this)
    if x.type.is_array():
        # DuckDB's `len(l)` of a list (#812): `UnFn.cardinality`.
        return E(_fn("cardinality", [x.json], dt.int64), dt.int64)
    (s_,) = _strings(lf, [x], "length")
    return E(_fn("character_length", [s_], dt.int64), dt.int64)


def _trim(lf: _Lift, node: sge.Trim, sub: Sub, scope: list[Column]) -> E:
    # DuckDB trims spaces, or the characters given.
    position = (node.args.get("position") or "BOTH").upper()
    name = {"BOTH": "btrim", "LEADING": "ltrim", "TRAILING": "rtrim"}.get(position)
    if name is None or node.args.get("collation"):
        raise SqlUnsupported(f"{_shown(node)} is not supported yet", construct="function trim")
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
            raise SqlUnsupported(
                f"substring with a {e.type} position is not supported",
                construct="function substring",
            )
        if a is length and e.constant and e.value is not None and e.value < 0:
            raise SqlUnsupported(
                "substring with a negative length is not supported yet",
                construct="function substring",
            )
        args.append(lf.to(e, dt.int64).json)
    if start is None:
        raise SqlUnsupported("substring needs a start", construct="function substring")
    opt = _option("negative_start", "WRAP_FROM_END")
    return E(_fn("substring", args, dt.string, [opt]), dt.string)


def _strpos(lf: _Lift, node: sge.StrPosition, sub: Sub, scope: list[Column]) -> E:
    # 1-based, 0 if absent; `strpos(s, '')` is 1.
    if node.args.get("position") is not None or node.args.get("occurrence") is not None:
        raise SqlUnsupported(f"{_shown(node)} is not supported yet", construct="function strpos")
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
            raise SqlUnsupported(
                f"{name.upper()} with a pattern that is not a constant",
                issue=319,
                construct=name.upper(),
            )
        if isinstance(p.value, str) and "\\" in p.value:
            raise SqlUnsupported(
                f"{name.upper()} with a backslash in the pattern is not supported yet",
                construct=name.upper(),
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
        raise Unsupported(
            "replace needs a constant pattern and replacement", construct="function replace"
        )
    args = _strings(lf, [sub(node.this), pattern, replacement], "replace")
    if pattern.value == "":
        # An empty pattern matches nowhere (D44, duckdb-replace-empty-pattern):
        # the string unchanged, NULL for a NULL replacement.
        return lf.to(replacement if replacement.value is None else sub(node.this), dt.string)
    return E(_fn("replace", args, dt.string), dt.string)


def _repeat(lf: _Lift, node: sge.Repeat, sub: Sub, scope: list[Column]) -> E:
    n = sub(node.args["times"])
    if not (n.type.is_integer() or n.type.is_null()):
        raise SqlUnsupported(f"repeat by a {n.type} is not supported", construct="function repeat")
    (s_,) = _strings(lf, [sub(node.this)], "repeat")
    return E(_fn("repeat", [s_, lf.to(n, dt.int64).json], dt.string), dt.string)


def _left(lf: _Lift, node: sge.Left, sub: Sub, scope: list[Column]) -> E:
    # The first `n` characters; a negative `n` is not supported.
    n = sub(node.expression)
    if not (n.constant and isinstance(n.value, int) and n.value >= 0):
        raise SqlUnsupported(
            "left needs a constant count of 0 or more",
            CONSTANT_FIX,
            construct="function left",
        )
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
        raise SqlUnsupported(
            "SHA2 of a length other than 256 is not supported", construct="function sha2"
        )
    (s_,) = _strings(lf, [sub(node.this)], "sha256")
    return E(_fn("sha256", [s_], dt.string), dt.string)


# -- regular expressions, padding, splitting (#808) ---------------------------


def _const(e: E, what: str, kind: type) -> Any:
    """The value of a constant argument of type `kind` (None for NULL)."""
    if not e.constant or not (e.value is None or isinstance(e.value, kind)):
        raise SqlUnsupported(
            f"{what} needs a constant {kind.__name__}",
            CONSTANT_FIX,
            construct=f"function {what.partition(chr(39))[0]}",
        )
    if isinstance(e.value, bool):
        raise SqlUnsupported(
            f"{what} needs a constant {kind.__name__}",
            CONSTANT_FIX,
            construct=f"function {what.partition(chr(39))[0]}",
        )
    return e.value


def _pattern(lf: _Lift, node: sge.Expression, sub: Sub, what: str) -> tuple[Json, str]:
    """The string and the constant pattern of a regular expression function."""
    p = sub(node.expression)
    if not (p.constant and isinstance(p.value, str)):
        raise SqlUnsupported(
            f"{what} needs a constant pattern",
            CONSTANT_FIX,
            construct=f"function {what}",
        )
    if not simple_regex(p.value):
        raise SqlUnsupported(
            f"the regular expression {p.value!r} is outside the supported subset",
            construct=f"function {what}",
        )
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
            raise SqlUnsupported(
                f"{what} with options is not supported yet", construct=f"function {what}"
            )
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
        raise SqlUnsupported(
            f"{_shown(node)} is not supported yet", construct="function regexp_extract"
        )
    if node.args.get("parameters") is not None:
        raise SqlUnsupported(
            "regexp_extract with options is not supported yet", construct="function regexp_extract"
        )
    s_, p = _pattern(lf, node, sub, "regexp_extract")
    group = node.args.get("group")
    g = 0 if group is None else _const(sub(group), "regexp_extract's group", int)
    if g is None or g < 0 or g > 9:
        # DuckDB raises past group 9 ("Group index must be between 0 and 9").
        raise SqlUnsupported(
            "regexp_extract needs a group number from 0 to 9", construct="function regexp_extract"
        )
    args = [s_, literal(p, dt.string), literal(g, dt.int64)]
    return E(call("regexp_extract", args), dt.string)


def _regexp_replace(lf: _Lift, node: sge.RegexpReplace, sub: Sub, scope: list[Column]) -> E:
    # The first match, or every match with the flag `'g'`.
    for k in ("position", "occurrence"):
        if node.args.get(k) is not None:
            raise SqlUnsupported(
                f"{_shown(node)} is not supported yet", construct="function regexp_replace"
            )
    flags = node.args.get("modifiers")
    flag = None if flags is None else _const(sub(flags), "regexp_replace's options", str)
    if flag not in (None, "g"):
        raise SqlUnsupported(
            f"regexp_replace with the options {flag!r} is not supported (only 'g')",
            construct="function regexp_replace",
        )
    s_, p = _pattern(lf, node, sub, "regexp_replace")
    r = sub(node.args["replacement"])
    if not (r.constant and isinstance(r.value, str)):
        raise SqlUnsupported(
            "regexp_replace needs a constant replacement",
            CONSTANT_FIX,
            construct="function regexp_replace",
        )
    args = [s_, literal(p, dt.string), literal(r.value, dt.string)]
    if flag == "g":
        args.append(literal("g", dt.string))
    return E(call("regexp_replace", args), dt.string)


def _right_of(lf: _Lift, s: E, n: E) -> E:
    """`right(s, n)` for an `n` that is not a constant (#1942): the same cases
    as the constant rule, chosen by comparisons, so that no start leaves the
    range of offsets `substring` takes (`n + size < 0` is `-n` past the end)."""
    if not n.type.is_integer():
        raise SqlUnsupported(f"right by a {n.type} is not supported", construct="function right")
    (s_,) = _strings(lf, [s], "right")
    n_ = lf.to(n, dt.int64).json
    i64 = lambda v: literal(v, dt.int64)  # noqa: E731
    size = call("character_length", [s_])
    neg = call("lt", [n_, i64(0)])
    ifs = [
        (logical("or", [call("is_null", [s_]), call("is_null", [n_])], eager=True),
         literal(None, dt.string)),
        (logical("and", [neg, call("lt", [call("add", [n_, size]), i64(0)])], eager=True),
         literal("", dt.string)),
        (neg, call("substring", [s_, call("subtract", [i64(1), n_])])),
        (call("gte", [n_, size]), s_),
    ]  # fmt: skip
    start = call("add", [call("subtract", [size, n_]), i64(1)])
    return E(if_then(ifs, call("substring", [s_, start])), dt.string)


def _right(lf: _Lift, node: sge.Right, sub: Sub, scope: list[Column]) -> E:
    # The last `n` characters, or all but the first `-n` for a negative `n`.
    n_e = sub(node.expression)
    if not n_e.constant:
        return _right_of(lf, sub(node.this), n_e)
    n = _const(n_e, "right", int)
    (s_,) = _strings(lf, [sub(node.this)], "right")
    if n is None:
        return _null(dt.string)
    if n < 0:
        # `1 - n` is past any string's end. It is capped at the largest offset
        # DuckDB's substring takes (2**32 - 1); `n = -2**63` gives 2**63 + 1,
        # which does not fit an i64.
        start = min(1 - n, 2**32 - 1)
        return E(_fn("substring", [s_, literal(start, dt.int64)], dt.string), dt.string)
    size = call("character_length", [s_])
    start = call("add", [call("subtract", [size, literal(n, dt.int64)]), literal(1, dt.int64)])
    return E(substring_left([s_, start]), dt.string)


#: The longest `lpad` or `rpad` the lift writes, in characters: its fill is a
#: constant of `n` characters, and `lpad('', 1100000000, '😀')` (DuckDB's
#: test_pad.test, which DuckDB refuses) built 4.4 GB of it (#2135).
PAD_MAX = 2**20


def _pad(lf: _Lift, node: sge.Pad, sub: Sub, scope: list[Column]) -> E:
    """`lpad(s, n, p)`, `rpad(s, n, p)`: the first `n` characters of `s`, or
    `s` filled to `n` characters with `p` repeated and cut, as DuckDB pads.
    For a constant `n` and `p`; DuckDB raises for `p = ''` where `s` is
    shorter than `n`."""
    left = bool(node.args.get("is_left"))
    what = "lpad" if left else "rpad"
    fill = node.args.get("fill_pattern")
    if fill is None:
        raise SqlUnsupported(f"{what} needs a fill", construct=f"function {what}")
    n = _const(sub(node.expression), what, int)
    p = _const(sub(fill), f"{what}'s fill", str)
    (s_,) = _strings(lf, [sub(node.this)], what)
    if n is None or p is None:
        return _null(dt.string)
    if n <= 0:
        return E(if_then([(call("is_null", [s_]), literal(None, dt.string))],
                         literal("", dt.string)), dt.string)  # fmt: skip
    if p == "":
        raise SqlUnsupported(
            f"{what} with an empty fill: DuckDB raises where the string is shorter",
            construct=f"function {what}",
        )
    if n > PAD_MAX:
        raise SqlUnsupported(
            f"{what} to more than {PAD_MAX} characters: the lift writes the fill as a "
            "constant of that many characters",
            construct=f"function {what}",
            hint=f"write a width of at most {PAD_MAX}, or pad in the engine's SQL after the "
            "checked plan",
        )
    size = call("character_length", [s_])
    cut = call("substring", [s_, literal(1, dt.int64), literal(n, dt.int64)])
    # The fill is the first `n - size` characters of `p` repeated: those of
    # a constant from the left of its beginning.
    # `p` repeated only as often as `n` needs: at most `n + len(p)` characters.
    filler = literal((p * -(-n // len(p)))[:n], dt.string)
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
        raise SqlUnsupported("concat_ws needs a value to join", construct="function concat_ws")
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

"""String rules of the Ibis producer, with LIKE, regular expressions and digests.

Part of the Ibis producer (`sverify.ibis_substrait`), derived from
ibis-substrait (Apache License 2.0); `__init__.py` notes the changes.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import Any

import ibis.expr.datatypes as dt
import ibis.expr.operations as ops

from sverify.ibis_substrait._base import Exprs, _unary, register, register_refusals
from sverify.plan_json import Json, Unsupported, call, chain, if_then, literal, substring_left

_URL_PARTS = ("Authority", "File", "Fragment", "Host", "Path", "Protocol", "Query", "UserInfo")


def _string_contains(x: Exprs, op: Any) -> Json:
    return call("gt", [call("strpos", [x(op.haystack), x(op.needle)]), literal(0, dt.int64)])


def _like(name: str) -> Callable[[Exprs, Any], Json]:
    def rule(x: Exprs, op: Any) -> Json:
        if op.escape is not None:
            raise Unsupported(f"{name.upper()} with an escape character is not supported")
        return call(name, [x(op.arg), x(op.pattern)])

    return rule


def _trim(name: str) -> Callable[[Exprs, Any], Json]:
    whitespace = " \t\n\r\x0b\x0c"
    return lambda x, op: call(name, [x(op.arg), literal(whitespace, dt.string)])


def _substring(x: Exprs, op: Any) -> Json:
    # Ibis counts from 0, and from the end for negative starts.
    if isinstance(op.length, ops.Literal) and op.length.value < 0:
        raise Unsupported("substring with a negative length")
    start = call("add", [x(op.start, dt.int64), literal(1, dt.int64)])
    start = if_then(
        [(call("gte", [start, literal(1, dt.int64)]), start)],
        call("add", [start, call("character_length", [x(op.arg)])]),
    )
    args = [x(op.arg), start] + ([] if op.length is None else [x(op.length, dt.int64)])
    return substring_left(args)


def _string_slice(x: Exprs, op: Any) -> Json:
    # Ibis's rewrite: `end - start` characters from `start` (0 if omitted).
    start = ops.Literal(0, dt.int64) if op.start is None else op.start
    if op.end is None:
        length = None
    elif isinstance(start, ops.Literal) and isinstance(op.end, ops.Literal):
        length = ops.Literal(op.end.value - start.value, dt.int64)
    else:
        length = ops.Subtract(op.end, start)
    return _substring(x, ops.Substring(op.arg, start=start, length=length))


def _capitalize(x: Exprs, op: Any) -> Json:
    # Ibis's rewrite: the first character in upper case, the rest in lower case.
    arg, one = x(op.arg), literal(1, dt.int64)
    first = call("upper", [call("substring", [arg, one, one])])
    rest = call("lower", [call("substring", [arg, literal(2, dt.int64)])])
    return call("str_concat", [first, rest])


def _pad(left: bool) -> Callable[[Exprs, Any], Json]:
    def rule(x: Exprs, op: Any) -> Json:
        # Ibis's DataFusion SQL: `s` if it has `length` characters or more,
        # otherwise `pad` repeated `length - length(s)` times on that side (a
        # longer `pad` is not cut to `length`).
        arg, n = x(op.arg), x(op.length, dt.int64)
        size = call("character_length", [arg])
        fill = call("repeat", [x(op.pad), call("subtract", [n, size])])
        padded = call("str_concat", [fill, arg] if left else [arg, fill])
        return if_then([(call("lte", [n, size]), arg)], padded)

    return rule


def _str_right(x: Exprs, op: Any) -> Json:
    # DataFusion's `right(s, n)`: the last `n` characters, or all but the
    # first `-n` for a negative `n`.
    arg, n, one = x(op.arg), x(op.nchars, dt.int64), literal(1, dt.int64)
    last = call("add", [call("subtract", [call("character_length", [arg]), n]), one])
    start = if_then([(call("lt", [n, literal(0, dt.int64)]), call("subtract", [one, n]))], last)
    return substring_left([arg, start])


def _replace(x: Exprs, op: Any) -> Json:
    if not isinstance(op.pattern, ops.Literal) or not isinstance(op.replacement, ops.Literal):
        raise Unsupported("replace needs a constant pattern and replacement")
    return call("replace", [x(op.arg), x(op.pattern), x(op.replacement)])


def _string_join(x: Exprs, op: Any) -> Json:
    # `concat_ws(sep, …)`: the arguments that are not NULL, joined by `sep`
    # ('' if all are NULL, NULL if `sep` is). Each is `sep || a`, or '' for a
    # NULL `a`; the first `sep` is dropped.
    sep, empty = x(op.sep), literal("", dt.string)
    parts = [call("coalesce", [call("str_concat", [sep, x(a)]), empty]) for a in op.arg]
    start = call("add", [call("character_length", [sep]), literal(1, dt.int64)])
    return call("substring", [chain("str_concat", parts), start])


def _find_in_set(x: Exprs, op: Any) -> Json:
    # Ibis's DataFusion SQL: `array_position(make_array(values), needle) - 1`,
    # -1 if absent; NULL finds a NULL value.
    needle = x(op.needle)
    ifs = [
        (call("is_not_distinct_from", [needle, x(v)]), literal(k, dt.int64))
        for k, v in enumerate(op.values)
    ]
    return if_then(ifs, literal(-1, dt.int64))


def _translate(x: Exprs, op: Any) -> Json:
    raise Unsupported("translate: DataFusion replaces grapheme clusters, not characters")


def _string_concat(x: Exprs, op: Any) -> Json:
    # NULL if any argument is: `str_concat` propagates NULLs.
    return chain("str_concat", [x(a) for a in op.arg])


def _regex_search(x: Exprs, op: Any) -> Json:
    if not isinstance(op.pattern, ops.Literal):
        raise Unsupported("regular expressions must be constants")
    arg, pattern = x(op.arg), x(op.pattern)
    matches = call("array_length", [call("regexp_match", [arg, pattern])])
    found = call(
        "coalesce", [call("gt", [matches, literal(0, dt.int64)]), literal(False, dt.boolean)]
    )
    return if_then([(call("is_null", [arg]), literal(None, dt.boolean))], found)


def _regex_extract(x: Exprs, op: Any) -> Json:
    if not isinstance(op.pattern, ops.Literal) or not isinstance(op.index, ops.Literal):
        raise Unsupported("re_extract needs a constant pattern and group")
    return call("regexp_extract", [x(op.arg), x(op.pattern), x(op.index, dt.int64)])


def _regex_replace(x: Exprs, op: Any) -> Json:
    if not isinstance(op.pattern, ops.Literal) or not isinstance(op.replacement, ops.Literal):
        raise Unsupported("re_replace needs a constant pattern and replacement")
    # Every match, as Ibis's SQL does (DuckDB's flag `'g'`).
    args = [x(op.arg), x(op.pattern), x(op.replacement), literal("g", dt.string)]
    return call("regexp_replace", args)


def _hex_digest(x: Exprs, op: Any) -> Json:
    if op.how not in ("md5", "sha256") or not op.arg.dtype.is_string():
        raise Unsupported(
            f"hexdigest({op.how!r}) of {op.arg.dtype} is not supported; "
            "md5 and sha256 of strings are"
        )
    return call(op.how, [x(op.arg)])


def _string_find(x: Exprs, op: Any) -> Json:
    # Ibis counts from 0 (-1 when absent): one less than `strpos`.
    if op.end is not None:
        raise Unsupported("find with an end is not supported")
    arg, sub, one = x(op.arg), x(op.substr), literal(1, dt.int64)
    if op.start is None:
        return call("subtract", [call("strpos", [arg, sub]), one])
    # Ibis's DataFusion SQL: from `start`, as
    # `COALESCE(NULLIF(strpos(substring(s, start + 1), t) + start, start), 0) - 1`.
    start = x(op.start, dt.int64)
    rest = substring_left([arg, call("add", [start, one])])
    pos = call("add", [call("strpos", [rest, sub]), start])
    found = call("coalesce", [call("nullif", [pos, start]), literal(0, dt.int64)])
    return call("subtract", [found, one])


register(
    {
        ops.Uppercase: _unary("upper"),
        ops.Lowercase: _unary("lower"),
        ops.StringLength: _unary("character_length"),
        ops.StartsWith: lambda x, op: call("starts_with", [x(op.arg), x(op.start)]),
        ops.EndsWith: lambda x, op: call("ends_with", [x(op.arg), x(op.end)]),
        ops.StringContains: _string_contains,
        ops.StringSQLLike: _like("like"),
        ops.StringSQLILike: _like("ilike"),
        ops.Strip: _trim("btrim"),
        ops.LStrip: _trim("ltrim"),
        ops.RStrip: _trim("rtrim"),
        ops.Substring: _substring,
        ops.StringSlice: _string_slice,
        ops.Capitalize: _capitalize,
        ops.LPad: _pad(left=True),
        ops.RPad: _pad(left=False),
        ops.Repeat: lambda x, op: call("repeat", [x(op.arg), x(op.times, dt.int64)]),
        ops.Reverse: _unary("reverse"),
        ops.StrRight: _str_right,
        ops.StringReplace: _replace,
        ops.StringAscii: _unary("ascii"),
        ops.StringJoin: _string_join,
        ops.FindInSet: _find_in_set,
        ops.Levenshtein: lambda x, op: call("levenshtein", [x(op.left), x(op.right)]),
        ops.Translate: _translate,
        ops.StringConcat: _string_concat,
        ops.RegexSearch: _regex_search,
        ops.RegexExtract: _regex_extract,
        ops.RegexReplace: _regex_replace,
        ops.HexDigest: _hex_digest,
        ops.StringFind: _string_find,
    }
)


register_refusals(
    {
        "Hash": "hash() is the engine's own and changes between versions; use hexdigest('md5') "
        "or hexdigest('sha256')",
        # Ibis's URL parts: `host()`, `protocol()`, …
        **dict.fromkeys(
            [f"Extract{p}" for p in _URL_PARTS],
            "URL parts are not modelled; extract them with re_extract",
        ),
    }
)

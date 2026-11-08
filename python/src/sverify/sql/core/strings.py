"""Strings: sequences of Unicode scalar values (`core/Sverify/Core/Text.lean`).

The string functions of `mkCall`, their SQL and their kinds. A function of
strings alone is a row of the function table (`sverify._functions`), which
gives its operation, kind and SQL; the others go here, with their `Dialect`
hooks in the strings section of `_base.Dialect`.
"""

from __future__ import annotations

from collections.abc import Callable

from sverify import _functions, _plan_read
from sverify.sql.core._base import (
    Bin,
    Expr,
    FixedKind,
    Kind,
    Lit,
    Un,
    Unsupported,
    _Writer,
    like_pattern,
    register,
)

SUBSTR_MAX, REPEAT_MAX = _plan_read.SUBSTR_MAX, _plan_read.REPEAT_MAX


def unicode_classes(p: str) -> bool:
    """Does the pattern use `\\d`, `\\w`, `\\s` or `\\b` (or their negations)?
    Rust's are Unicode classes; RE2's (DuckDB), Java's (Spark) and Snowflake's
    are ASCII-only, so they agree on ASCII text only (`Text.classesDiffer`)."""
    i = 0
    while i < len(p):
        if p[i] == "\\" and i + 1 < len(p):
            if p[i + 1] in "dDwWsSbB":
                return True
            i += 2
        else:
            i += 1
    return False


def regex_groups(p: str) -> int:
    """The entries `regexp_match(s, p)` has on a match (`_plan_read.regex_groups`)."""
    return _plan_read.regex_groups(p, Unsupported)


def call(name: str, args: list[Expr]) -> Expr | None:
    """`mkCall`'s strings functions."""
    match name, args:
        # Strings (`core/Sverify/Core/Text.lean`); the table's are `_base.table_call`'s.
        # The third argument is the escape character; NULL means a backslash.
        case "like", ([a, b] | [a, b, Lit(value=None)]):
            return Bin("like", a, b)
        case "like", [_, _, _]:
            raise Unsupported(
                "LIKE … ESCAPE is not modelled yet; match a literal % or _ with contains "
                "or starts_with"
            )
        case "substring", [a, b]:
            return Bin("substr", a, b)
        case "substring", [a, b, Lit(value=int(n))] if not isinstance(n, bool):
            if n < 0:
                raise Unsupported("a negative substring length always fails")
            return Bin("substr", a, b, length=n)
        case "substring", [_, _, _]:
            raise Unsupported("substring lengths must be constants")
        case (("btrim" | "ltrim" | "rtrim"), [a, *rest]) if len(rest) <= 1:
            chars = rest[0] if rest else Lit(" ", "str")
            sides = {"btrim": (True, True), "ltrim": (True, False), "rtrim": (False, True)}[name]
            return Bin("trim", a, chars, sides=sides)
        case "replace", [a, Lit(value=str(pattern)), Lit(value=str(replacement))]:
            return Un("replace", a, param=pattern, replacement=replacement)
        case "replace", [_, _, _]:
            raise Unsupported("replace needs a constant pattern and replacement")
        case "ilike", ([a, b] | [a, b, Lit(value=None)]):
            return Bin("ilike", a, b)
        case "ilike", [_, _, _]:
            raise Unsupported(
                "ILIKE … ESCAPE is not modelled yet; match a literal % or _ with contains "
                "or starts_with on lower(…)"
            )
        case "regexp_match", _:
            raise Unsupported("regexp_match is only supported as array_length(regexp_match(s, p))")
        # A constant pattern (#50); `Text.simpleRegex` is checked in Lean.
        case "regexp_extract", [a, Lit(value=str(pattern))]:
            return Un("regex_extract", a, param=pattern)
        case "regexp_extract", [a, Lit(value=str(pattern)), Lit(value=int(g))] if (
            not isinstance(g, bool) and g >= 0
        ):
            return Un("regex_extract", a, param=pattern, digits=g)
        case "regexp_extract", _:
            raise Unsupported("regexp_extract needs a constant pattern and group")
        case "regexp_replace", [a, Lit(value=str(pattern)), Lit(value=str(r))]:
            return Un("regex_replace", a, param=pattern, replacement=r)
        case "regexp_replace", [a, Lit(value=str(pattern)), Lit(value=str(r)), Lit(value="g")]:
            return Un("regex_replace", a, param=pattern, replacement=r, flags="g")
        case "regexp_replace", [_, _, _, *_]:
            raise Unsupported(
                "regexp_replace needs a constant pattern and replacement, and no flags but 'g'"
            )
    return None


def expr(
    self: _Writer, e: Expr, ref: Callable[[int], str], cols: list[Kind | None], ctx: Kind | None
) -> str | None:
    """`_Writer.expr` of the strings operations."""
    d = self.d

    match e:
        case Un(op=op, arg=a) if op in _TABLE:
            return _table(self, _TABLE[op], [a], ref, cols)
        case Bin(op=op, left=a, right=b) if op in _TABLE:
            return _table(self, _TABLE[op], [a, b], ref, cols)
        case Un(op="regex_match", arg=a, param=pattern):
            groups = regex_groups(pattern)
            x = self.operand(a, "str", ref, cols, "regexp_match")
            m = d.case_when(d.regex_search(x, pattern), d.int_lit(groups), d.null("int"))
            return (
                self.ascii_only(x, m, f"regular expression {pattern!r}", "int")
                if (unicode_classes(pattern))
                else m
            )
        case Bin(op="like" | "ilike" as op, left=a, right=b):
            sa, sb = (self.operand(x, "str", ref, cols, op.upper()) for x in (a, b))
            if isinstance(b, Lit):
                pattern = None if b.value is None else d.str_lit(like_pattern(b.value))
            else:
                pattern = d.like_pattern(sb)
            if pattern is None:
                return d.null("bool")
            if op == "like":
                return d.like(sa, pattern)
            # A black box: Unicode case folding, which engines do with their own tables.
            text = sa if isinstance(b, Lit) and b.value.isascii() else d.concat(sa, sb)
            return self.ascii_only(text, d.ilike(sa, pattern), "ILIKE", "bool")
        case Un(op="regex_extract", arg=a, param=pattern, digits=group):
            x = self.operand(a, "str", ref, cols, "regexp_extract")
            v = d.regex_extract(x, pattern, group)
            if unicode_classes(pattern):
                return self.ascii_only(x, v, f"regular expression {pattern!r}")
            return v
        case Un(op="regex_replace", arg=a, param=pattern, replacement=r, flags=flags):
            x = self.operand(a, "str", ref, cols, "regexp_replace")
            v = d.regex_replace(x, pattern, r, flags == "g")
            if unicode_classes(pattern):
                return self.ascii_only(x, v, f"regular expression {pattern!r}")
            return v
        case Un(op="replace", arg=a, param=pattern, replacement=replacement):
            if not pattern:
                # Rust puts the replacement around every character; SQL engines
                # return the string unchanged.
                raise Unsupported("replace with an empty pattern differs between engines")
            x = self.operand(a, "str", ref, cols, "replace")
            return d.replace(x, d.str_lit(pattern), d.str_lit(replacement))
        case Bin(op="repeat", left=a, right=b):
            sa = self.operand(a, "str", ref, cols, "repeat")
            n = self.int_operand(b, ref, cols, "repeat")
            r = d.repeat(sa, n)
            if not d.guards:
                return r
            # `Text.repeatFits`; the count capped so that the product fits.
            cap = d.int_lit(REPEAT_MAX + 1)
            capped = f"(CASE WHEN {n} > {cap} THEN {cap} ELSE {n} END)"
            big = f"({capped} * {d.octet_length(sa)} > {d.int_lit(REPEAT_MAX)})"
            fail = d.raise_("repeat beyond 2^31 - 1 bytes", sa, "str")
            return d.case_when(big, fail, r)
        case Bin(op="substr", left=a, right=b, length=length, param=start):
            sa = self.operand(a, "str", ref, cols, "substring")
            sb = self.int_operand(b, ref, cols, "substring")
            if start != "LEFT_OF_BEGINNING" and not (
                isinstance(b, Lit) and isinstance(b.value, int) and b.value >= 0
            ):
                # `Text.substrWrap`: a negative start counts from the end.
                shifted = d.int_add(d.int_add(sb, d.char_length(sa)), d.int_lit(1))
                wrapped = f"(CASE WHEN {sb} < {d.int_lit(0)} THEN {shifted} ELSE {sb} END)"
                if d.guards:
                    # `Text.substrInRange` (#336): the engine raises on an
                    # offset out of range, but sees the shifted one here.
                    low = f"({sb} < {d.int_lit(-SUBSTR_MAX)})"
                    fail = d.raise_("substring offset outside of supported range", sa, "int")
                    wrapped = d.case_when(low, fail, wrapped)
                sb = wrapped
            return self.substring(sa, sb, length)
        case Bin(op="trim", left=a, right=b, sides=sides):
            sa, sb = (self.operand(x, "str", ref, cols, "trim") for x in (a, b))
            return d.trim(sa, sb, *sides)
    return None


#: The table's functions that the writer writes as their rows' SQL, by operation.
_TABLE = {f.op: f for f in _functions.area("strings") if f.expr}


def _table(
    self: _Writer,
    f: _functions.Fn,
    args: list[Expr],
    ref: Callable[[int], str],
    cols: list[Kind | None],
) -> str:
    """A row of the function table: its SQL of the operands, guarded where
    engines agree on ASCII text only (`ascii_only`)."""
    xs = [self.operand(a, k, ref, cols, f.what) for a, k in zip(args, f.args, strict=True)]
    sql = self.d.fn(f.name, *xs)
    if not f.ascii:
        return sql
    text = xs[0] if len(xs) == 1 else self.d.concat(*xs)
    return self.ascii_only(text, sql, f.ascii, f.result)  # type: ignore[arg-type]


#: The result kinds of this area's `Un` and `Bin` operations (`Expr.kind`).
UN_KINDS: dict[str, FixedKind] = _functions.kinds("strings", un=True)
BIN_KINDS: dict[str, FixedKind] = _functions.kinds("strings", un=False)

register(call, expr, un_kinds=UN_KINDS, bin_kinds=BIN_KINDS)

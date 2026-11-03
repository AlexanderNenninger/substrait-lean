"""Strings: sequences of Unicode scalar values (`SubstraitLean/Text.lean`).

The string functions of `mkCall`, their SQL and their kinds. A new string
function goes here, its `Dialect` hook in the strings section of `_base.Dialect`.
"""

from __future__ import annotations

from collections.abc import Callable

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

#: The longest string DataFusion's `repeat` writes, in bytes (`Text.repeatMax`).
REPEAT_MAX = 2**31 - 1


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
    """The entries `regexp_match(s, p)` has on a match: its capture groups, or
    the whole match if there are none. Groups are counted as `(` outside
    classes and escapes, but `(?:`, which is exact for patterns without
    other `(?`."""
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
                raise Unsupported(f"regular expressions with '(?' are not supported: {p!r}")
            else:
                groups += 1
        k += 1
    return max(groups, 1)


def call(name: str, args: list[Expr]) -> Expr | None:
    """`mkCall`'s strings functions."""
    match name, args:
        # Strings (`SubstraitLean/Text.lean`).
        case "upper", [a]:
            return Un("upper", a)
        case "lower", [a]:
            return Un("lower", a)
        case (("character_length" | "char_length" | "length"), [a]):
            return Un("length", a)
        case "str_concat", [a, b]:
            return Bin("concat", a, b)
        case "strpos", [a, b]:
            return Bin("strpos", a, b)
        case "starts_with", [a, b]:
            return Bin("starts_with", a, b)
        case "ends_with", [a, b]:
            return Bin("ends_with", a, b)
        # The third argument is the escape character; NULL means a backslash.
        case "like", ([a, b] | [a, b, Lit(value=None)]):
            return Bin("like", a, b)
        case "like", [_, _, _]:
            raise Unsupported("LIKE … ESCAPE is not supported (DataFusion only allows a backslash)")
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
        case "reverse", [a]:
            return Un("reverse", a)
        case "ascii", [a]:
            return Un("ascii", a)
        case "replace", [a, Lit(value=str(pattern)), Lit(value=str(replacement))]:
            return Un("replace", a, param=pattern, replacement=replacement)
        case "replace", [_, _, _]:
            raise Unsupported("replace needs a constant pattern and replacement")
        case "repeat", [a, b]:
            return Bin("repeat", a, b)
        case "ilike", ([a, b] | [a, b, Lit(value=None)]):
            return Bin("ilike", a, b)
        case "ilike", [_, _, _]:
            raise Unsupported(
                "ILIKE … ESCAPE is not supported (DataFusion only allows a backslash)"
            )
        case "levenshtein", [a, b]:
            return Bin("levenshtein", a, b)
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
        case (("md5" | "sha256"), [a]):
            return Un(name, a)
    return None


def expr(
    self: _Writer, e: Expr, ref: Callable[[int], str], cols: list[Kind | None], ctx: Kind | None
) -> str | None:
    """`_Writer.expr` of the strings operations."""
    d = self.d

    match e:
        case Un(op="length", arg=a):
            return d.char_length(self.operand(a, "str", ref, cols, "length"))
        case Un(op="upper" | "lower" as op, arg=a):
            x = self.operand(a, "str", ref, cols, op)
            return self.ascii_only(x, (d.upper if op == "upper" else d.lower)(x), op.upper())
        case Un(op="regex_match", arg=a, param=pattern):
            groups = regex_groups(pattern)
            x = self.operand(a, "str", ref, cols, "regexp_match")
            m = d.case_when(d.regex_search(x, pattern), d.int_lit(groups), d.null("int"))
            return (
                self.ascii_only(x, m, f"regular expression {pattern!r}", "int")
                if (unicode_classes(pattern))
                else m
            )
        case Bin(op="concat", left=a, right=b):
            sa, sb = (self.operand(x, "str", ref, cols, "||") for x in (a, b))
            return d.concat(sa, sb)
        case Bin(op="strpos" | "starts_with" | "ends_with" as op, left=a, right=b):
            sa, sb = (self.operand(x, "str", ref, cols, op) for x in (a, b))
            f = {"strpos": d.strpos, "starts_with": d.starts_with, "ends_with": d.ends_with}
            return f[op](sa, sb)
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
        case Un(op="reverse", arg=a):
            x = self.operand(a, "str", ref, cols, "reverse")
            return self.ascii_only(x, d.reverse(x), "reverse")
        case Un(op="ascii", arg=a):
            x = self.operand(a, "str", ref, cols, "ascii")
            return self.ascii_only(x, d.first_code_point(x), "ascii", "int")
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
        case Un(op="md5" | "sha256" as op, arg=a):
            return d.digest(op, self.operand(a, "str", ref, cols, op))
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
        case Bin(op="levenshtein", left=a, right=b):
            sa, sb = (self.operand(x, "str", ref, cols, "levenshtein") for x in (a, b))
            return self.ascii_only(d.concat(sa, sb), d.levenshtein(sa, sb), "levenshtein", "int")
        case Bin(op="substr", left=a, right=b, length=length, param=start):
            sa = self.operand(a, "str", ref, cols, "substring")
            sb = self.int_operand(b, ref, cols, "substring")
            if start != "LEFT_OF_BEGINNING" and not (
                isinstance(b, Lit) and isinstance(b.value, int) and b.value >= 0
            ):
                # `Text.substrWrap`: a negative start counts from the end.
                shifted = d.int_add(d.int_add(sb, d.char_length(sa)), d.int_lit(1))
                sb = f"(CASE WHEN {sb} < {d.int_lit(0)} THEN {shifted} ELSE {sb} END)"
            return self.substring(sa, sb, length)
        case Bin(op="trim", left=a, right=b, sides=sides):
            sa, sb = (self.operand(x, "str", ref, cols, "trim") for x in (a, b))
            return d.trim(sa, sb, *sides)
    return None


#: The result kinds of this area's `Un` and `Bin` operations (`Expr.kind`).
UN_KINDS: dict[str, FixedKind] = {
    "length": "int", "regex_match": "int", "ascii": "int", "upper": "str", "lower": "str",
    "reverse": "str", "replace": "str", "regex_extract": "str", "regex_replace": "str",
    "md5": "str", "sha256": "str",
}  # fmt: skip
BIN_KINDS: dict[str, FixedKind] = {
    "strpos": "int", "levenshtein": "int", "concat": "str", "substr": "str", "trim": "str",
    "repeat": "str",
}  # fmt: skip

register(call, expr, un_kinds=UN_KINDS, bin_kinds=BIN_KINDS)

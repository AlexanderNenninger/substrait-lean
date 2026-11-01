"""Substrait plans as SQL, with the semantics of the Lean `Rel` model.

`to_sql(plan, dialect)` reads a Substrait JSON plan the way
`SubstraitLean/Parse.lean` does, so it accepts exactly the plans the checker
accepts: the same operators, the same functions and the same constant folding,
with every other construct rejected (`Unsupported`). It then writes one SQL
query whose result is `Rel.eval` of the plan. Nothing is left to engine
defaults:

* Every subquery names its columns positionally (`c0`, `c1`, …), so field
  references are unambiguous whatever the input tables call their columns.
* Integers are `BIGINT`: operands are cast, and arithmetic must raise on
  overflow (Lean's integers are unbounded; a wrapped result would be wrong).
  Division and remainder truncate. Where DataFusion fails at run time
  (division by zero, `MIN / -1`, a bad `POWER` or `CAST(double AS BIGINT)`),
  Lean's value is NULL and `SubstraitLean/Safety.lean` says when that can
  happen; the SQL raises there too (`Dialect.raise_`).
* Doubles have one zero and one NaN (`SubstraitLean/Float.lean`): `-0.0` is
  `0.0`, NaN equals itself and is above `inf`, in comparisons, join
  conditions, groups, window partitions and sort keys. Every double read
  from a table, and every one an operation could make `-0.0`, goes through
  `Dialect.canon`, so `-0.0` never reaches a result.
* Filters keep a row only when the condition is TRUE, `AND`/`OR`/`NOT` are
  Kleene's, and every `ORDER BY` key says where NULLs go.
* Row order follows `Rel.eval`'s list order wherever it matters. Below a
  `FETCH` or a window, subqueries carry an ordinal column `o`: scan order for
  tables, row index for `VALUES`, left-major for joins, branch order for
  `UNION ALL` and sort order for windows. Window sorts break ties by it, as
  Lean's stable merge sort does, and the query's result is ordered by it when
  the plan has a `FETCH` or a window.

Engines differ in syntax and in a few semantics; those go through the hooks of
a `Dialect` (see `sverify.sql.duckdb`).
"""

from __future__ import annotations

import base64
import json
import math
import re
from collections.abc import Callable, Sequence
from dataclasses import dataclass, replace
from datetime import date, datetime, timedelta
from fractions import Fraction
from typing import Any, Literal

I64_MIN, I64_MAX = -(2**63), 2**63 - 1

Kind = Literal["int", "float", "time", "date", "interval", "str", "bool", "tod"]
"""What a value is in SQL. `time` is a microsecond TIMESTAMP without time
zone, `tod` a microsecond TIME of day, `interval` a day/second interval of
microseconds. `None` (unknown) is
used for columns whose Substrait type the model does not know."""

LeanKind = Literal["int", "float", "time", "date", "str", "bool", "tod", "other"]
"""`Parse.Kind`: what Lean's parser knows about a value. The parser decides
between integer and double arithmetic by it, so this module tracks it too."""


class Unsupported(ValueError):
    """The plan is outside the Lean model, or the dialect cannot express it.

    Raised by `sverify.engines.to_sql`, and so by `sverify.engines.run` on
    DuckDB and Spark and by `sverify.engines.run_spark`; the message says
    which construct, and for a dialect, why (e.g. Snowflake tables have no
    row order, so a `FETCH` cannot follow the model's). A subclass of
    `ValueError`. This is `sverify.engines.Unsupported`.
    """


# --------------------------------------------------------------------------
# Dialects


@dataclass(frozen=True)
class Dialect:
    """SQL syntax and semantics of one engine.

    Every hook takes SQL text for its operands (each already self-contained,
    e.g. parenthesised) and returns SQL text. The defaults are ANSI SQL;
    subclasses override what their engine writes differently and raise
    `Unsupported` for what it cannot do.

    Use one of the dialect objects rather than building one:
    `sverify.engines.DUCKDB`, `sverify.engines.SNOWFLAKE` and
    `sverify.engines.SPARK`. This is `sverify.engines.Dialect`.

    Attributes:
        name: The engine's name, used in `Unsupported` messages.
    """

    name: str
    guards: bool = True
    """Write the run-time checks of `SubstraitLean/Safety.lean`'s issues:
    64-bit overflow, division by zero, `date_trunc` out of range. Without them
    (`to_sql(..., guards=False)`) the SQL is only right for plans whose
    contract report is `guard_free` (`Rel.guardFree_sound` in
    `SubstraitLean/Guards.lean`). Integer `SUM` keeps its check."""

    # Identifiers and types

    def quote(self, ident: str) -> str:
        return '"' + ident.replace('"', '""') + '"'

    def type_name(self, kind: Kind) -> str:
        return {
            "int": "BIGINT",
            "float": "DOUBLE PRECISION",
            "time": "TIMESTAMP",
            "date": "DATE",
            "tod": "TIME",
            "interval": "INTERVAL",
            "str": "VARCHAR",
            "bool": "BOOLEAN",
        }[kind]

    def cast(self, sql: str, kind: Kind) -> str:
        return f"CAST({sql} AS {self.type_name(kind)})"

    def result_kind(self, kind: Kind | None) -> None:
        """Raise `Unsupported` if a result column cannot have this kind."""

    # Literals

    def null(self, kind: Kind | None) -> str:
        return "NULL" if kind is None else self.cast("NULL", kind)

    def bool_lit(self, b: bool) -> str:
        return "TRUE" if b else "FALSE"

    def int_lit(self, i: int) -> str:
        """A BIGINT constant; `i` is in the 64-bit range."""
        return self.cast(str(i), "int")

    def float_lit(self, f: float) -> str:
        """A double: NaN, ±inf, or a number (`-0.0` is `0.0`)."""
        if math.isnan(f):
            return self.cast("'NaN'", "float")
        if f == 0:
            return self.cast("'0'", "float")
        if math.isinf(f):
            return self.cast("'Infinity'" if f > 0 else "'-Infinity'", "float")
        return self.cast(f"'{f!r}'", "float")

    def str_lit(self, s: str) -> str:
        return "'" + s.replace("'", "''") + "'"

    def timestamp_lit(self, micros: int) -> str:
        return f"TIMESTAMP '{_timestamp_text(micros)}'"

    def date_lit(self, days: int) -> str:
        return f"DATE '{_date_text(days)}'"

    def time_of_day_lit(self, micros: int) -> str:
        s, us = divmod(micros, 1_000_000)
        return f"TIME '{s // 3600:02}:{s // 60 % 60:02}:{s % 60:02}.{us:06}'"

    def interval_lit(self, micros: int) -> str:
        sign = "-" if micros < 0 else ""
        d, rest = divmod(abs(micros), 86_400_000_000)
        s, us = divmod(rest, 1_000_000)
        h, s = divmod(s, 3600)
        m, s = divmod(s, 60)
        return f"INTERVAL '{sign}{d} {h:02}:{m:02}:{s:02}.{us:06}' DAY TO SECOND"

    # Integer arithmetic on BIGINT operands; must raise on 64-bit overflow.

    def int_add(self, a: str, b: str) -> str:
        return f"({a} + {b})"

    def int_sub(self, a: str, b: str) -> str:
        return f"({a} - {b})"

    def int_mul(self, a: str, b: str) -> str:
        return f"({a} * {b})"

    def int_neg(self, a: str) -> str:
        return f"(- {a})"

    def raise_(self, message: str, dep: str, kind: Kind) -> str:
        """An expression of type `kind` that fails at run time with `message`
        when evaluated (and is NULL when `dep` is NULL). Only evaluated in a
        `CASE` branch that needs it."""
        raise Unsupported(f"{self.name} has no way to raise an error at run time")

    def trunc_div(self, a: str, b: str) -> str:
        """`a / b` rounded toward zero, for `b <> 0`; must raise on `MIN / -1`."""
        raise Unsupported(f"{self.name}: integer division is not implemented")

    def trunc_mod(self, a: str, b: str) -> str:
        """The remainder of `trunc_div`, with the sign of `a`, for `b` not 0 or -1."""
        raise Unsupported(f"{self.name}: integer remainder is not implemented")

    def int_div(self, a: str, b: str) -> str:
        """`BinFn.idiv`: truncating; division by zero raises (Lean: NULL), but
        `NULL / 0` is NULL, as in `Safety.lean` (only integers divide)."""
        if not self.guards:
            return self.trunc_div(a, b)
        fail = self.raise_("division by zero", b, "int")
        return (
            f"(CASE WHEN {a} IS NULL THEN {self.null('int')} WHEN {b} = {self.int_lit(0)} "
            f"THEN {fail} ELSE {self.trunc_div(a, b)} END)"
        )

    def int_mod(self, a: str, b: str) -> str:
        """`BinFn.imod`: the sign of `a`; by zero raises (Lean: NULL), by -1 is 0;
        `NULL % 0` is NULL."""
        zero = self.int_mul(a, self.int_lit(0))
        if not self.guards:
            # `MIN % -1` fails on some engines; that branch is semantics, not a check.
            return (
                f"(CASE WHEN {b} = {self.int_lit(-1)} THEN {zero} ELSE {self.trunc_mod(a, b)} END)"
            )
        fail = self.raise_("division by zero", b, "int")
        return (
            f"(CASE WHEN {a} IS NULL THEN {self.null('int')} WHEN {b} = {self.int_lit(0)} "
            f"THEN {fail} WHEN {b} = {self.int_lit(-1)} THEN {zero} "
            f"ELSE {self.trunc_mod(a, b)} END)"
        )

    def int_pow(self, a: str, b: int) -> str:
        """`BinFn.ipow` with a constant exponent: a negative exponent, or a
        result outside 64 bits, raises (Lean: NULL); NULL stays NULL."""
        null = self.null("int")
        if b < 0:
            fail = self.raise_("negative exponent", a, "int")
            return f"(CASE WHEN {a} IS NULL THEN {null} ELSE {fail} END)"
        if b > 64:
            # Only -1, 0 and 1 have powers that fit; `a * a` is |a| for them.
            small = a if b % 2 else self.int_mul(a, a)
            fail = self.raise_("integer overflow", a, "int")
            lo, hi = self.int_lit(-1), self.int_lit(1)
            return (
                f"(CASE WHEN {a} IS NULL THEN {null} WHEN {a} >= {lo} AND {a} <= {hi} "
                f"THEN {small} ELSE {fail} END)"
            )
        if b == 0:
            return f"(CASE WHEN {a} IS NULL THEN {null} ELSE {self.int_lit(1)} END)"
        # Partial products grow in magnitude, so checked multiplication raises
        # exactly when the result leaves 64 bits.
        out = a
        for _ in range(b - 1):
            out = self.int_mul(out, a)
        return out

    def int_product(self, a: str, n: str) -> str:
        """`a` multiplied `n` times (1 ≤ n ≤ 64), raising on 64-bit overflow."""
        raise Unsupported(f"{self.name}: POWER with a non-constant exponent is not implemented")

    def int_pow_var(self, a: str, b: str) -> str:
        """`BinFn.ipow` with an exponent column: as `int_pow`, row by row."""
        null, one = self.null("int"), self.int_lit(1)
        lo, sixty_four = self.int_lit(-1), self.int_lit(64)
        small = (
            f"(CASE WHEN {self.trunc_mod(b, self.int_lit(2))} = {one} "
            f"THEN {a} ELSE {self.int_mul(a, a)} END)"
        )
        big = (
            f"(CASE WHEN {a} >= {lo} AND {a} <= {one} THEN {small} "
            f"ELSE {self.raise_('integer overflow', a, 'int')} END)"
        )
        return (
            f"(CASE WHEN {a} IS NULL OR {b} IS NULL THEN {null} "
            f"WHEN {b} < {self.int_lit(0)} THEN {self.raise_('negative exponent', b, 'int')} "
            f"WHEN {b} = {self.int_lit(0)} THEN {one} WHEN {b} > {sixty_four} THEN {big} "
            f"ELSE {self.int_product(a, b)} END)"
        )

    # Doubles: IEEE 754, so x / 0 is ±inf or NaN rather than an error.

    def float_add(self, a: str, b: str) -> str:
        return f"({a} + {b})"

    def float_sub(self, a: str, b: str) -> str:
        return f"({a} - {b})"

    def float_mul(self, a: str, b: str) -> str:
        return f"({a} * {b})"

    def float_div(self, a: str, b: str) -> str:
        return f"({a} / {b})"

    def float_neg(self, a: str) -> str:
        """IEEE negation; NaN stays NaN (`canon` makes `-0.0` zero)."""
        return f"(- {a})"

    def canon(self, x: str) -> str:
        """`x` with `-0.0` made `0.0`, the model's one zero: IEEE's
        `-0.0 + 0.0` is `0.0`, and other values stay (`x` appears once)."""
        return f"({x} + {self.float_lit(0.0)})"

    def int_to_float(self, a: str) -> str:
        return self.cast(a, "float")

    def int_to_str(self, a: str) -> str:
        """Decimal digits with a leading `-` for negatives (Lean's `toString`)."""
        return self.cast(a, "str")

    def float_floor(self, x: str) -> str:
        """Exact; NaN/±inf stay (a zero result goes through `canon`)."""
        return f"FLOOR({x})"

    def float_ceil(self, x: str) -> str:
        """Exact; NaN/±inf stay."""
        return f"CEIL({x})"

    def float_round(self, x: str) -> str:
        """To an integer, halves away from zero; NaN/±inf stay."""
        return f"ROUND({x})"

    def float_round_to(self, x: str, digits: int) -> str:
        """`ROUND(x, d)` as DataFusion computes it: `round(x · 10ᵈ) / 10ᵈ`."""
        p = self.float_lit(10.0**digits)
        return self.float_div(self.float_round(self.float_mul(x, p)), p)

    def float_pow(self, a: str, b: str) -> str:
        """C's `pow`: IEEE results, no errors."""
        return f"POWER({a}, {b})"

    # Elementary functions and bitwise operations (`SubstraitLean/Numeric.lean`).
    # The writer guards their domains, so the hooks only see arguments inside them.

    def float_fn(self, name: str, x: str) -> str:
        """An elementary function (`FMath.name`) of a double in its domain, as
        C's `libm` computes it (±inf and NaN in, IEEE results out)."""
        return f"{name.upper()}({x})"

    def float_atan2(self, y: str, x: str) -> str:
        """C's `atan2`, for `(y, x)` other than `(0, 0)`."""
        return f"ATAN2({y}, {x})"

    def float_logb(self, x: str, b: str) -> str:
        """`ln x / ln b`, for positive `x` and `b`, `b` not 1."""
        return self.float_div(self.float_fn("ln", x), self.float_fn("ln", b))

    def bitwise(self, op: str, a: str, b: str) -> str:
        """A `BitOp` (`BitOp.name`) of 64-bit integers, in two's complement; a
        shift's count `b` is in `0`–`63`, and bits shifted out are lost."""
        raise Unsupported(f"{self.name}: {op} is not implemented")

    def float_to_int(self, x: str) -> str:
        """`CAST(x AS BIGINT)`: truncation toward zero; NaN, ±inf and values
        outside 64 bits must raise (Lean: NULL)."""
        raise Unsupported(f"{self.name}: CAST(double AS BIGINT) is not implemented")

    def is_nan(self, x: str) -> str:
        """TRUE for NaN, NULL for NULL."""
        return f"({x} <> {x})"

    def float_rank(self, x: str) -> str:
        """1 for NaN, 0 for other doubles, NULL for NULL: NaN is above `inf`."""
        return f"(CASE WHEN {x} IS NULL THEN NULL WHEN {self.is_nan(x)} THEN 1 ELSE 0 END)"

    def float_eq(self, a: str, b: str) -> str:
        """Equality of doubles: NaN = NaN (IEEE has NaN <> NaN)."""
        ra, rb = self.float_rank(a), self.float_rank(b)
        return f"({ra} = {rb} AND ({ra} = 1 OR {a} = {b}))"

    def float_lt(self, a: str, b: str) -> str:
        """`<` of doubles: NaN is above everything else."""
        ra, rb = self.float_rank(a), self.float_rank(b)
        return f"({ra} < {rb} OR ({ra} = 0 AND {rb} = 0 AND {a} < {b}))"

    # Timestamps and intervals

    def time_add_interval(self, ts: str, iv: str) -> str:
        return f"({ts} + {iv})"

    def time_sub_interval(self, ts: str, iv: str) -> str:
        return f"({ts} - {iv})"

    def time_diff(self, a: str, b: str) -> str:
        """`a - b` for timestamps, as an interval."""
        return f"({a} - {b})"

    def interval_add(self, a: str, b: str) -> str:
        return f"({a} + {b})"

    def interval_sub(self, a: str, b: str) -> str:
        return f"({a} - {b})"

    def date_part(self, part: str, ts: str) -> str:
        """`Time.datePart` of a timestamp: the proleptic Gregorian calendar,
        `week` the ISO week, `dow` from Sunday = 0, `millisecond` and
        `microsecond` within the minute; NULL outside the dates chrono
        represents (the years -262143 to 262142)."""
        raise Unsupported(f"{self.name}: date_part is not implemented")

    def date_trunc(self, unit: str, ts: str) -> str:
        """`Time.trunc`: rounded down to the unit, weeks from Monday."""
        raise Unsupported(f"{self.name}: date_trunc is not implemented")

    def to_date(self, ts: str) -> str:
        """`UnFn.toDate`: the calendar day of a timestamp (rounding down)."""
        return self.cast(ts, "date")

    def time_part(self, part: str, t: str) -> str:
        """`Time.partOf` of a time of day, for its clock parts (`millisecond`
        and `microsecond` within the minute)."""
        return self.date_part(part, f"(DATE '1970-01-01' + {t})")

    def time_of_day(self, ts: str) -> str:
        """`Time.timeOfDay`: the TIME of a timestamp."""
        return self.cast(ts, "tod")

    def as_time(self, us: str) -> str:
        """`UnFn.asTime`: the timestamp `us` microseconds after 1970-01-01."""
        raise Unsupported(f"{self.name}: timestamps from microseconds are not implemented")

    def zero_pad(self, n: str, width: int) -> str:
        """The integer `n ≥ 0` in decimal, padded with zeros to `width` digits
        (`lpad` would cut a longer one)."""
        s = self.int_to_str(n)
        pad = f"lpad({s}, {width}, '0')"
        return f"(CASE WHEN {self.char_length(s)} >= {width} THEN {s} ELSE {pad} END)"

    def time_micros(self, ts: str) -> str:
        """A timestamp as microseconds since 1970-01-01 (a BIGINT)."""
        raise Unsupported(f"{self.name}: timestamps as microseconds are not implemented")

    def date_days(self, d: str) -> str:
        """A DATE as days since 1970-01-01 (a BIGINT)."""
        return f"({d} - DATE '1970-01-01')"

    def date_to_time(self, d: str) -> str:
        """The midnight of a DATE, for one `chrono` represents."""
        return self.cast(d, "time")

    def date_add_days(self, d: str, n: str) -> str:
        """`BinFn.dateAdd`: `n` days after the DATE `d`."""
        return f"({d} + {n})"

    def date_diff_days(self, a: str, b: str) -> str:
        """`BinFn.dateDiff`: the days from `b` to `a`."""
        return f"({self.date_days(a)} - {self.date_days(b)})"

    def add_months(self, x: str, months: int, kind: Kind) -> str:
        """`Time.addMonths`: the same day `months` months later, clamped to
        the end of that month (`kind` is `date` or `time`)."""
        raise Unsupported(f"{self.name}: adding months is not implemented")

    # Strings: sequences of Unicode scalar values (`SubstraitLean/Text.lean`).
    # Lengths and positions count characters, and string order (which only
    # sorts use) is by code point, i.e. byte order: no collation.

    def upper(self, s: str) -> str:
        """A black box in Lean, meaning Rust's `str::to_uppercase` (DataFusion's
        and Polars'). SQL engines map case with their own tables (`'ß'`), so
        the writer guards it with `is_ascii`."""
        return f"UPPER({s})"

    def lower(self, s: str) -> str:
        return f"LOWER({s})"

    def char_length(self, s: str) -> str:
        return f"CHAR_LENGTH({s})"

    def is_ascii(self, s: str) -> str:
        """Is every character of `s` ASCII? (Its UTF-8 bytes are its characters.)"""
        return f"(OCTET_LENGTH({s}) = {self.char_length(s)})"

    def concat(self, a: str, b: str) -> str:
        """NULL if either is."""
        return f"({a} || {b})"

    def strpos(self, s: str, t: str) -> str:
        """The 1-based position of the first `t` in `s`, 0 if none, 1 for ''."""
        return f"POSITION({t} IN {s})"

    def starts_with(self, s: str, t: str) -> str:
        return f"starts_with({s}, {t})"

    def ends_with(self, s: str, t: str) -> str:
        return f"ends_with({s}, {t})"

    def like(self, s: str, pattern: str) -> str:
        """`s LIKE pattern` with `\\` as the escape character; the pattern has
        no trailing lone backslash (`like_pattern`)."""
        return f"({s} LIKE {pattern} ESCAPE {self.str_lit(chr(92))})"

    def like_pattern(self, p: str) -> str:
        """`like_pattern` of a computed pattern: a backslash appended when `p`
        ends with an odd number of them."""
        raise Unsupported(f"{self.name}: LIKE with a computed pattern is not implemented")

    def substring(self, s: str, start: str, length: str | None) -> str:
        """Characters from 1-based `start` ≥ 1 on (`length` of them)."""
        n = "" if length is None else f" FOR {length}"
        return f"SUBSTRING({s} FROM {start}{n})"

    def trim(self, s: str, chars: str, left: bool, right: bool) -> str:
        """Remove characters of the set `chars` from the start and/or end."""
        side = "BOTH" if left and right else "LEADING" if left else "TRAILING"
        return f"TRIM({side} {chars} FROM {s})"

    def octet_length(self, s: str) -> str:
        """The size of `s` in UTF-8 bytes."""
        return f"OCTET_LENGTH({s})"

    def repeat(self, s: str, n: str) -> str:
        """`s` `n` times, '' for `n ≤ 0`."""
        return f"REPEAT({s}, CASE WHEN {n} < {self.int_lit(0)} THEN {self.int_lit(0)} ELSE {n} END)"

    def reverse(self, s: str) -> str:
        """The characters of `s` backwards; engines that reverse grapheme
        clusters agree on ASCII text (the writer guards it)."""
        return f"REVERSE({s})"

    def replace(self, s: str, pattern: str, replacement: str) -> str:
        """Every non-overlapping `pattern` (not empty) from the left."""
        return f"REPLACE({s}, {pattern}, {replacement})"

    def first_code_point(self, s: str) -> str:
        """The code point of the first character, 0 for '' (ASCII `s` only)."""
        return f"ASCII({s})"

    def ilike(self, s: str, pattern: str) -> str:
        """`LIKE` ignoring case (ASCII text only), with `like`'s escapes."""
        return f"({s} ILIKE {pattern} ESCAPE {self.str_lit(chr(92))})"

    def levenshtein(self, s: str, t: str) -> str:
        """The edit distance in characters (ASCII text only)."""
        return f"LEVENSHTEIN({s}, {t})"

    def regex_search(self, s: str, pattern: str) -> str:
        """Does the regular expression (a constant) match somewhere in `s`?
        Regular expressions are black boxes in Lean; each engine has its
        own dialect, which agrees with Rust's on simple patterns."""
        raise Unsupported(f"{self.name}: regular expressions are not implemented")

    # Aggregates

    def int_sum(self, v: str) -> str:
        """`SUM` of the BIGINT column `v`, exactly; a sum outside 64 bits
        raises (DataFusion wraps around, Lean's sum is the true one)."""
        raise Unsupported(f"{self.name}: integer SUM is not implemented")

    def float_sum(self, v: str, o: str) -> str:
        """`floatSum`: the doubles of `v` added one by one in the order of the
        ordinal `o`, from +0.0 (rounding depends on the order)."""
        raise Unsupported(f"{self.name}: SUM of doubles in row order is not implemented")

    # Three-valued logic and comparisons (NULL-propagating)

    def eq(self, a: str, b: str) -> str:
        return f"({a} = {b})"

    def lt(self, a: str, b: str) -> str:
        return f"({a} < {b})"

    def and3(self, a: str, b: str) -> str:
        return f"({a} AND {b})"

    def or3(self, a: str, b: str) -> str:
        return f"({a} OR {b})"

    def not3(self, a: str) -> str:
        return f"(NOT {a})"

    def is_null(self, a: str) -> str:
        return f"({a} IS NULL)"

    def is_true(self, a: str) -> str:
        """TRUE when `a` is TRUE, FALSE when it is FALSE or NULL."""
        return f"({a} IS TRUE)"

    def case_when(self, c: str, t: str, e: str) -> str:
        """`t` when `c` is TRUE, else `e` (also when `c` is NULL)."""
        return f"(CASE WHEN {c} THEN {t} ELSE {e} END)"

    # Ordering and windows

    def sort_key(self, expr: str, desc: bool, nulls_first: bool, kind: Kind | None = None) -> str:
        """One ORDER BY key; `kind` is what `expr` is (a double's sort is
        already split into rank and value keys)."""
        return f"{expr} {'DESC' if desc else 'ASC'} NULLS {'FIRST' if nulls_first else 'LAST'}"

    def over(self, partition: Sequence[str], order: Sequence[str]) -> str:
        parts = []
        if partition:
            parts.append("PARTITION BY " + ", ".join(partition))
        if order:
            parts.append("ORDER BY " + ", ".join(order))
        return f"OVER ({' '.join(parts)})"

    def row_number(self, over: str) -> str:
        return f"ROW_NUMBER() {over}"

    def over_frame(self, partition: Sequence[str], order: Sequence[str], frame: str) -> str:
        """`OVER (PARTITION BY … ORDER BY … frame)`."""
        return self.over(partition, order)[:-1] + f" {frame})"

    def day_interval(self, days: int) -> str:
        """`days` days, as a RANGE offset over a DATE."""
        return f"INTERVAL '{days}' DAY"

    def window_int_sum(self, v: str, over: str) -> str:
        """`SUM` of BIGINTs over a frame; must raise where it leaves 64 bits."""
        raise Unsupported(f"{self.name}: window sums are not implemented")

    def window_float_sum(self, v: str, over: str) -> str:
        """`floatSum`: the frame's doubles added left to right, from 0.0."""
        raise Unsupported(
            f"{self.name} does not add a frame's doubles in order, and the rounding depends on it"
        )

    def lag(self, x: str, offset: int, default: str, over: str) -> str:
        return f"LAG({x}, {offset}, {default}) {over}"

    def lead(self, x: str, offset: int, default: str, over: str) -> str:
        return f"LEAD({x}, {offset}, {default}) {over}"

    # Relations

    def row_ordinal(self) -> str:
        """An expression numbering a base table's rows in a fixed scan order,
        used where Lean's list order matters (below FETCH and windows)."""
        raise Unsupported(f"{self.name} has no stable row order for tables")

    def subquery(self, select: str, alias: str) -> str:
        return f"({select}) AS {alias}"

    def values(self, rows: Sequence[Sequence[str]], columns: Sequence[str]) -> str:
        """A FROM item with these rows (at least one) and column names."""
        body = ", ".join("(" + ", ".join(r) + ")" for r in rows)
        return f"(VALUES {body}) AS v({', '.join(columns)})"

    def limit_offset(self, offset: int, count: int | None) -> str:
        parts = [] if count is None else [f"LIMIT {count}"]
        if offset:
            parts.append(f"OFFSET {offset}")
        return " ".join(parts)

    def cross_join(self, left: str, right: str) -> str:
        return f"{left} CROSS JOIN {right}"

    def union_all(self, a: str, b: str) -> str:
        return f"{a} UNION ALL {b}"


def _timestamp_text(micros: int) -> str:
    try:
        ts = datetime(1970, 1, 1) + timedelta(microseconds=micros)
    except OverflowError as e:
        raise Unsupported(f"timestamp {micros}µs is out of range") from e
    return ts.strftime("%Y-%m-%d %H:%M:%S.%f")


def _date_text(days: int) -> str:
    try:
        return (date(1970, 1, 1) + timedelta(days=days)).isoformat()
    except OverflowError as e:
        raise Unsupported(f"date {days} is out of range") from e


# --------------------------------------------------------------------------
# The model: `Expr` and `Rel` of the Lean development


@dataclass(frozen=True)
class Lit:
    """A constant. `value` is None (NULL), bool, int, str or float; `kind`
    says what an int is (integer, microseconds, days) and types NULLs."""

    value: Any
    kind: Kind | None


@dataclass(frozen=True)
class Field:
    index: int


@dataclass(frozen=True)
class Un:
    op: Literal[
        "not", "is_null", "neg", "itof", "fneg", "ffloor", "fceil", "fround", "froundTo",
        "ftoi", "narrow", "itos", "upper", "lower", "length", "regex_match", "date_part",
        "date_trunc", "to_date", "day_part", "day_trunc", "add_months", "time_of_day", "as_time",
        "strftime", "bucket", "reverse", "ascii", "replace", "fmath",
    ]  # fmt: skip
    arg: Expr
    digits: int = 0
    """The `d` of `froundTo d`, the bits of `narrow`, the months of `addMonths`."""
    param: str = ""
    """The pattern of `regexMatch` and `replace`, the part of `datePart`, the
    unit of `dateTrunc`; `time` or `date` for `addMonths`; the function of
    `fmath` (`FMath.name`)."""
    origin: int = 0
    """The origin of `bucket` (whose width is `digits`)."""
    replacement: str = ""
    """The replacement of `replace`."""


@dataclass(frozen=True)
class Bin:
    op: Literal[
        "add", "sub", "mul", "eq", "lt", "and", "or", "fadd", "fsub", "fmul", "fdiv",
        "idiv", "imod", "ipow", "fpow", "concat", "strpos", "starts_with", "ends_with",
        "like", "substr", "trim", "date_add", "date_diff", "repeat", "ilike", "levenshtein",
        "fatan2", "flogb", "bit",
    ]  # fmt: skip
    left: Expr
    right: Expr
    length: int | None = None
    """The `n` of `substr n`."""
    sides: tuple[bool, bool] = (True, True)
    """`left` and `right` of `trim`."""
    param: str = ""
    """The operation of `bit` (`BitOp.name`)."""


#: `FMath.name`: elementary functions of a double (`SubstraitLean/Numeric.lean`).
FMATH = (
    "sqrt", "exp", "ln", "log10", "log2", "sin", "cos", "tan", "asin", "acos", "atan",
)  # fmt: skip
#: `BitOp.name`: bitwise operations of integers.
BITWISE = (
    "bitwise_and", "bitwise_or", "bitwise_xor", "bitwise_shift_left", "bitwise_shift_right",
)  # fmt: skip
#: `Parse.doubleFns`: functions of doubles only.
DOUBLE_FNS = ("atan2", "logb", *FMATH)


@dataclass(frozen=True)
class If:
    cond: Expr
    then: Expr
    orelse: Expr


Expr = Lit | Field | Un | Bin | If


@dataclass(frozen=True)
class SortKey:
    col: int
    desc: bool
    nulls_first: bool


@dataclass(frozen=True)
class Frame:
    """`Window.Frame`: `ROWS` or `RANGE`, each bound `("unbounded" | "preceding"
    | "following", k)`; `("preceding", 0)` is `CURRENT ROW`."""

    range: bool
    lo: tuple[str, int]
    hi: tuple[str, int]


WHOLE = Frame(False, ("unbounded", 0), ("unbounded", 0))


@dataclass(frozen=True)
class WinFn:
    fn: Literal[
        "row_number", "lag", "lead", "rank", "dense_rank", "percent_rank", "cume_dist", "ntile",
        "agg", "first_value", "last_value", "nth_value",
    ]  # fmt: skip
    col: int = 0
    offset: int = 0
    """`LAG`'s offset, `NTILE`'s buckets, `NTH_VALUE`'s n."""
    default: Lit = Lit(None, None)
    measure: Measure | None = None
    """The aggregate of `agg`."""
    frame: Frame = WHOLE

    @property
    def reads(self) -> bool:
        """Does it read column `col`?"""
        return self.fn in ("lag", "lead", "first_value", "last_value", "nth_value")


@dataclass(frozen=True)
class Read:
    name: tuple[str, ...]
    columns: tuple[str, ...]
    kinds: tuple[Kind | None, ...]
    lean_kinds: tuple[LeanKind, ...]


@dataclass(frozen=True)
class Values:
    arity: int
    rows: tuple[tuple[Expr, ...], ...]
    kinds: tuple[Kind | None, ...]
    lean_kinds: tuple[LeanKind, ...]


@dataclass(frozen=True)
class Filter:
    input: Rel
    cond: Expr


@dataclass(frozen=True)
class Project:
    input: Rel
    exprs: tuple[Expr, ...]


@dataclass(frozen=True)
class Emit:
    input: Rel
    mapping: tuple[int, ...]


@dataclass(frozen=True)
class Cross:
    left: Rel
    right: Rel


@dataclass(frozen=True)
class Join:
    left: Rel
    right: Rel
    type: Literal["inner", "left"]
    on: Expr


@dataclass(frozen=True)
class Fetch:
    input: Rel
    offset: int
    count: int | None


@dataclass(frozen=True)
class UnionAll:
    left: Rel
    right: Rel


@dataclass(frozen=True)
class Window:
    input: Rel
    part: tuple[int, ...]
    sort: tuple[SortKey, ...]
    fns: tuple[WinFn, ...]


@dataclass(frozen=True)
class Semi:
    """The left rows with some (`anti`: no) right row satisfying `on`."""

    left: Rel
    right: Rel
    anti: bool
    on: Expr


@dataclass(frozen=True)
class OrderBy:
    """A stable sort."""

    input: Rel
    keys: tuple[SortKey, ...]


@dataclass(frozen=True)
class Distinct:
    """The first occurrence of every row."""

    input: Rel


@dataclass(frozen=True)
class Measure:
    """`fn` of `arg` over the rows `filter` keeps (`SubstraitLean/Aggregate.lean`)."""

    fn: Literal["count", "sum", "fsum", "avg", "min", "max"]
    arg: Expr
    distinct: bool = False
    filter: Expr | None = None


@dataclass(frozen=True)
class Aggregate:
    """`GROUP BY groups`, then one column per measure."""

    input: Rel
    groups: tuple[Expr, ...]
    measures: tuple[Measure, ...]


Rel = (
    Read | Values | Filter | Project | Emit | Cross | Join | Fetch | UnionAll | Window | Semi
    | OrderBy | Distinct | Aggregate
)  # fmt: skip


# Kinds of columns and expressions. `kinds` is what SQL sees; `lean_kinds`
# mirrors `Rel.kinds`/`Expr.kind`, which the parser's choices depend on.


def kinds(r: Rel) -> list[Kind | None]:
    match r:
        case Read() | Values():
            return list(r.kinds)
        case Filter(input=i) | Fetch(input=i) | OrderBy(input=i) | Distinct(input=i):
            return kinds(i)
        case Semi(left=a):
            return kinds(a)
        case Aggregate(input=i, groups=gs, measures=ms):
            ks = kinds(i)
            return [expr_kind(g, ks) for g in gs] + [_measure_kind(m, ks, expr_kind) for m in ms]
        case Project(input=i, exprs=es):
            ks = kinds(i)
            return ks + [expr_kind(e, ks) for e in es]
        case Emit(input=i, mapping=m):
            ks = kinds(i)
            return [ks[j] if j < len(ks) else None for j in m]
        case Cross(left=a, right=b) | Join(left=a, right=b):
            return kinds(a) + kinds(b)
        case UnionAll(left=a):
            return kinds(a)
        case Window(input=i, fns=fns):
            ks = kinds(i)
            return ks + [_win_kind(f, ks, None) for f in fns]


def lean_kinds(r: Rel) -> list[LeanKind]:
    match r:
        case Read():
            return list(r.lean_kinds)
        case Values():
            # `Rel.kinds` reads them from the `baseSchema`, as for tables.
            return list(r.lean_kinds)
        case Filter(input=i) | Fetch(input=i) | OrderBy(input=i) | Distinct(input=i):
            return lean_kinds(i)
        case Semi(left=a):
            return lean_kinds(a)
        case Aggregate(input=i, groups=gs, measures=ms):
            ks = lean_kinds(i)
            return [lean_expr_kind(g, ks) for g in gs] + [
                _measure_kind(m, ks, lean_expr_kind) for m in ms
            ]
        case Project(input=i, exprs=es):
            ks = lean_kinds(i)
            return ks + [lean_expr_kind(e, ks) for e in es]
        case Emit(input=i, mapping=m):
            ks = lean_kinds(i)
            return [ks[j] if j < len(ks) else "other" for j in m]
        case Cross(left=a, right=b) | Join(left=a, right=b):
            return lean_kinds(a) + lean_kinds(b)
        case UnionAll(left=a):
            return lean_kinds(a)
        case Window(input=i, fns=fns):
            ks = lean_kinds(i)
            return ks + [_win_kind(f, ks, "other") for f in fns]


def _win_kind[K](f: WinFn, cols: list[K], unknown: K) -> Any:
    """`WinFn.kind`."""
    if f.fn in ("row_number", "rank", "dense_rank", "ntile"):
        return "int"
    if f.fn in ("percent_rank", "cume_dist"):
        return "float"
    if f.fn == "agg" and f.measure is not None:
        m = f.measure
        if m.fn in ("count", "sum"):
            return "int"
        if m.fn in ("fsum", "avg"):
            return "float"
        return (
            cols[m.arg.index] if isinstance(m.arg, Field) and m.arg.index < len(cols) else unknown
        )
    return cols[f.col] if f.col < len(cols) else unknown


def _measure_kind[K](m: Measure, cols: list[K], kind: Callable[[Expr, list[K]], Any]) -> Any:
    """`Measure.kind`."""
    if m.fn in ("count", "sum"):
        return "int"
    return "float" if m.fn in ("fsum", "avg") else kind(m.arg, cols)


def _issue_free(e: Expr) -> bool:
    """`Parse.issueFree`: columns, constants and their conversions to doubles."""
    match e:
        case Lit() | Field():
            return True
        case Un(op="itof", arg=a):
            return _issue_free(a)
    return False


def _get(ks: list, i: int) -> Any:
    return ks[i] if i < len(ks) else None


def _lean_lit_kind(v: Any) -> LeanKind:
    # `litKind`: doubles, timestamps, dates and intervals are all `Value.int`.
    if v is None:
        return "other"
    if isinstance(v, bool):
        return "bool"
    return "str" if isinstance(v, str) else "int"


def lean_expr_kind(e: Expr, cols: list[LeanKind]) -> LeanKind:
    match e:
        case Lit(value=v):
            return _lean_lit_kind(v)
        case Field(index=i):
            return cols[i] if i < len(cols) else "other"
        case Un(op="neg", arg=a):
            return lean_expr_kind(a, cols)
        case Un(op="itof" | "fneg" | "ffloor" | "fceil" | "fround" | "froundTo" | "fmath"):
            return "float"
        case Un(
            op="ftoi" | "narrow" | "length" | "regex_match" | "date_part" | "day_part" | "ascii"
        ):
            return "int"
        case Un(op="itos" | "upper" | "lower" | "reverse" | "replace"):
            return "str"
        case Un(op="date_trunc"):
            return "time"
        case Un(op="to_date" | "day_trunc"):
            return "date"
        case Un(op="add_months", param=k):
            return "time" if k == "time" else "date"
        case Un(op="time_of_day"):
            return "tod"
        case Un(op="as_time" | "bucket"):
            return "time"
        case Un(op="strftime"):
            return "str"
        case Un():
            return "bool"
        case Bin(op="add" | "sub" | "mul", left=a, right=b):
            return lean_expr_kind(b if isinstance(a, Lit) else a, cols)
        case Bin(op="fadd" | "fsub" | "fmul" | "fdiv" | "fpow" | "fatan2" | "flogb"):
            return "float"
        case Bin(op="idiv" | "imod" | "ipow" | "strpos" | "date_diff" | "levenshtein" | "bit"):
            return "int"
        case Bin(op="date_add"):
            return "date"
        case Bin(op="concat" | "substr" | "trim" | "repeat"):
            return "str"
        case Bin():
            return "bool"
        case If(then=Lit(value=v), orelse=o):
            return _lean_lit_kind(v) if isinstance(o, Lit) else lean_expr_kind(o, cols)
        case If(then=t):
            return lean_expr_kind(t, cols)


def expr_kind(e: Expr, cols: list[Kind | None]) -> Kind | None:
    match e:
        case Lit(kind=k):
            return k
        case Field(index=i):
            return _get(cols, i)
        case Un(op="neg", arg=a):
            return expr_kind(a, cols)
        case Un(op="itof" | "fneg" | "ffloor" | "fceil" | "fround" | "froundTo" | "fmath"):
            return "float"
        case Un(
            op="ftoi" | "narrow" | "length" | "regex_match" | "date_part" | "day_part" | "ascii"
        ):
            return "int"
        case Un(op="itos" | "upper" | "lower" | "reverse" | "replace"):
            return "str"
        case Un(op="date_trunc"):
            return "time"
        case Un(op="to_date" | "day_trunc"):
            return "date"
        case Un(op="add_months", param=k):
            return "time" if k == "time" else "date"
        case Un(op="time_of_day"):
            return "tod"
        case Un(op="as_time" | "bucket"):
            return "time"
        case Un(op="strftime"):
            return "str"
        case Un():
            return "bool"
        case Bin(op="date_diff"):
            return "int"
        case Bin(op="date_add"):
            return "date"
        case Bin(op="add" | "sub", left=a, right=b):
            ka, kb = expr_kind(a, cols), expr_kind(b, cols)
            if ka == "time" and kb == "time":
                return "interval"
            return ka if ka in ("time", "interval") or kb is None else kb
        case Bin(op="mul", left=a, right=b):
            return expr_kind(a, cols) or expr_kind(b, cols)
        case Bin(op="fadd" | "fsub" | "fmul" | "fdiv" | "fpow" | "fatan2" | "flogb"):
            return "float"
        case Bin(op="idiv" | "imod" | "ipow" | "strpos" | "levenshtein" | "bit"):
            return "int"
        case Bin(op="concat" | "substr" | "trim" | "repeat"):
            return "str"
        case Bin():
            return "bool"
        case If(then=t, orelse=o):
            return expr_kind(t, cols) or expr_kind(o, cols)


# --------------------------------------------------------------------------
# Parsing: a transcription of `SubstraitLean/Parse.lean`


def _field(j: dict, k: str) -> Any:
    """`field?`: a present, non-null member."""
    v = j.get(k) if isinstance(j, dict) else None
    return v


def _req(j: dict, k: str) -> Any:
    v = _field(j, k)
    if v is None:
        raise Unsupported(f"missing field '{k}' in {_short(j)}")
    return v


def _short(j: Any) -> str:
    s = json.dumps(j, separators=(",", ":"))
    return s if len(s) <= 80 else s[:80] + "…"


def _arr(j: dict, k: str) -> list:
    v = _field(j, k)
    if v is None:
        return []
    if not isinstance(v, list):
        raise Unsupported(f"expected an array in '{k}'")
    return v


def _int(j: Any) -> int:
    if isinstance(j, bool):
        raise Unsupported(f"expected integer, got {j!r}")
    if isinstance(j, int):
        return j
    if isinstance(j, str) and re.fullmatch(r"-?\d+", j):
        return int(j)
    raise Unsupported(f"expected integer, got {j!r}")


def _nat(j: Any) -> int:
    i = _int(j)
    if i < 0:
        raise Unsupported(f"expected non-negative integer, got {i}")
    return i


def _nat_d(j: dict, k: str) -> int:
    v = _field(j, k)
    return 0 if v is None else _nat(v)


def _oneof(what: str, j: dict, keys: Sequence[str]) -> tuple[str, Any]:
    for k in keys:
        v = _field(j, k)
        if v is not None:
            return k, v
    raise Unsupported(f"unsupported {what}: {_short(j)}")


def _base_name(name: str) -> str:
    return name.split(":")[0]


def _type_kinds(ty: Any) -> tuple[LeanKind, Kind | None]:
    """`typeKind`, and the SQL kind of the same type."""
    if not isinstance(ty, dict):
        return "other", None
    if any(k in ty for k in ("i8", "i16", "i32", "i64")):
        return "int", "int"
    if any(k in ty for k in ("fp32", "fp64")):
        return "float", "float"
    if "timestamp" in ty:
        return "time", "time"
    if "precisionTimestamp" in ty:
        # Times are microseconds; a coarser precision is not modelled.
        pts = ty["precisionTimestamp"]
        if isinstance(pts, dict) and pts.get("precision", 0) >= 6:
            return "time", "time"
        return "other", None
    if "date" in ty:
        return "date", "date"
    if "time" in ty:
        return "tod", "tod"
    if "precisionTime" in ty:
        pt = ty["precisionTime"]
        if isinstance(pt, dict) and pt.get("precision", 0) >= 6:
            return "tod", "tod"
        return "other", None
    if any(k in ty for k in ("string", "varchar", "fixedChar")):
        return "str", "str"
    if "bool" in ty:
        return "bool", "bool"
    return "other", None


def _int_bits(ty: dict) -> int:
    """`Parse.intBits`: the width of an integer type."""
    return next((n for n in (8, 16, 32) if f"i{n}" in ty), 64)


def _lean_type_kind(ty: Any) -> LeanKind:
    return _type_kinds(ty)[0]


def _schema_types(schema: Any) -> list:
    st = _field(schema, "struct") if isinstance(schema, dict) else None
    types = _field(st, "types") if isinstance(st, dict) else None
    return types if isinstance(types, list) else []


@dataclass
class Const:
    """`Parse.Const`, plus what an integer stands for."""

    tag: Literal["int", "flt", "dec", "str", "bool", "null"]
    value: Any = None
    scale: int = 0
    kind: Kind | None = None

    def to_float(self) -> float | None:
        match self.tag:
            case "int":
                return float(self.value)
            case "flt":
                return self.value
            case "dec":
                return float(Fraction(self.value, 10**self.scale))
            case "str":
                t = self.value.strip().lower()
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
        return None

    def to_int(self) -> int | None:
        match self.tag:
            case "int":
                return self.value
            case "flt":
                if math.isnan(self.value) or math.isinf(self.value):
                    return None
                return _round_half_away(Fraction(self.value))
            case "dec":
                return _round_half_away(Fraction(self.value, 10**self.scale))
            case "str":
                t = self.value.strip()
                return int(t) if re.fullmatch(r"-?\d+", t) else None
        return None


def _round_half_away(x: Fraction) -> int:
    mag = math.floor(abs(x) + Fraction(1, 2))
    return -mag if x < 0 else mag


def _int_bits(ty: dict) -> int:
    for k, b in (("i8", 8), ("i16", 16), ("i32", 32)):
        if k in ty:
            return b
    return 64


_TIMESTAMP = re.compile(r"(\d+)-(\d+)-(\d+)(?: (\d+):(\d+):(\d+)(?:\.(\d*))?)?")


def _parse_date(s: str) -> int | None:
    m = re.fullmatch(r"(\d+)-(\d+)-(\d+)", s)
    if m is None:
        return None
    return _days_from_civil(*map(int, m.groups()))


def _days_from_civil(y: int, m: int, d: int) -> int:
    """`Time.daysFromCivil` (Lean's `/` and `%` on these operands floor)."""
    y = y - 1 if m <= 2 else y
    era = (y if y >= 0 else y - 399) // 400
    yoe = y - era * 400
    mp = (m + 9) % 12
    doy = (153 * mp + 2) // 5 + d - 1
    doe = yoe * 365 + yoe // 4 - yoe // 100 + doy
    return era * 146097 + doe - 719468


def _parse_timestamp(s: str) -> int | None:
    m = _TIMESTAMP.fullmatch(s)
    if m is None:
        return None
    y, mo, d, h, mi, sec, frac = m.groups()
    days = _days_from_civil(int(y), int(mo), int(d))
    if h is None:
        return days * 86_400_000_000
    micros = int((frac + "000000")[:6]) if frac else 0
    return ((days * 24 + int(h)) * 60 + int(mi)) * 60_000_000 + int(sec) * 1_000_000 + micros


def _wide_int_decimal(ty: Any) -> bool:
    """`Parse.wideIntDecimal`: a decimal of scale 0 and at least 19 digits,
    whose values the model keeps as integers."""
    d = ty.get("decimal") if isinstance(ty, dict) else None
    return isinstance(d, dict) and d.get("scale", 0) == 0 and d.get("precision", 0) >= 19


def _interval_type(ty: Any) -> bool:
    return isinstance(ty, dict) and ("intervalDayToSecond" in ty or "intervalCompound" in ty)


def _cast_const(ty: dict, c: Const) -> Const:
    lean, kind = _type_kinds(ty)
    if c.tag == "null":
        return Const("null", kind=kind)
    if _wide_int_decimal(ty):
        if c.tag == "int" or (c.tag == "dec" and c.scale == 0):
            return Const("int", c.value, kind="int")
        raise Unsupported("cannot cast this value to an integer decimal")
    match lean:
        case "float":
            f = c.to_float()
            if f is None:
                raise Unsupported("cannot cast this value to a double")
            return Const("flt", f, kind="float")
        case "int":
            i = c.to_int()
            if i is None:
                raise Unsupported("cannot cast this value to an integer")
            bits = _int_bits(ty)
            if not -(2 ** (bits - 1)) <= i < 2 ** (bits - 1):
                raise Unsupported(f"cast of {i} to a {bits}-bit integer overflows")
            return Const("int", i, kind="int")
        case "time" | "date":
            if c.tag == "str":
                parse = _parse_timestamp if lean == "time" else _parse_date
                v = parse(c.value.strip())
                if v is None:
                    raise Unsupported(
                        f"cannot parse {'timestamp' if lean == 'time' else 'date'} '{c.value}'"
                    )
                return Const("int", v, kind=lean)
            if c.tag == "int":
                return Const("int", c.value, kind=lean)
            raise Unsupported(
                f"cannot cast this value to a {'timestamp' if lean == 'time' else 'date'}"
            )
        case "str":
            if c.tag == "str":
                return c
            raise Unsupported("casts to strings are not supported")
    raise Unsupported("unsupported cast type")


def _interval_micros(d: dict) -> int:
    days = _int(_field(d, "days") or 0)
    secs = _int(_field(d, "seconds") or 0)
    sub = _int(_field(d, "subseconds") or 0)
    p = _nat_d(d, "precision")
    # Lean's `Int` division rounds toward negative infinity here (`Int.div` is `ediv`
    # for a positive divisor), like Python's `//`.
    sub_us = sub // 10 ** (p - 6) if p >= 6 else sub * 10 ** (6 - p)
    return (days * 86400 + secs) * 1_000_000 + sub_us


def _decode_decimal(s: str) -> int:
    try:
        raw = base64.b64decode(s, validate=False)
    except ValueError as e:
        raise Unsupported("malformed decimal literal") from e
    return int.from_bytes(raw, "little", signed=True) if raw else 0


_LITERAL_KEYS = (
    "boolean", "i8", "i16", "i32", "i64", "fp32", "fp64", "string", "null", "decimal",
    "precisionTimestamp", "timestamp", "date", "precisionTime", "time", "intervalDayToSecond",
    "intervalYearToMonth", "intervalCompound",
)  # fmt: skip


def _year_months(ym: dict) -> int:
    return 12 * _int(_field(ym, "years") or 0) + _int(_field(ym, "months") or 0)


_COMPARISONS = (
    "equal", "not_equal", "lt", "gt", "lte", "gte", "is_distinct_from", "is_not_distinct_from",
)  # fmt: skip


def _calendar_interval(j: Any) -> bool:
    """`calendarInterval`: an interval literal with days or months."""
    lit = _field(j, "literal")
    if lit is None:
        return False
    if (d := _field(lit, "intervalDayToSecond")) is not None:
        return _int(_field(d, "days") or 0) != 0
    if (ym := _field(lit, "intervalYearToMonth")) is not None:
        return _year_months(ym) != 0
    if (c := _field(lit, "intervalCompound")) is not None:
        ym, ds = _field(c, "intervalYearToMonth"), _field(c, "intervalDayToSecond")
        return (ym is not None and _year_months(ym) != 0) or (
            ds is not None and _int(_field(ds, "days") or 0) != 0
        )
    return False


def _interval_lit(j: Any) -> tuple[int, int] | None:
    """`intervalLit?`: an interval literal as months and microseconds."""
    lit = _field(j, "literal")
    if lit is None:
        return None
    if (d := _field(lit, "intervalDayToSecond")) is not None:
        return 0, _interval_micros(d)
    if (ym := _field(lit, "intervalYearToMonth")) is not None:
        return _year_months(ym), 0
    if (c := _field(lit, "intervalCompound")) is not None:
        ym, ds = _field(c, "intervalYearToMonth"), _field(c, "intervalDayToSecond")
        return (0 if ym is None else _year_months(ym)), (0 if ds is None else _interval_micros(ds))
    return None


def _const_literal(j: dict) -> Const:
    key, v = _oneof("literal", j, _LITERAL_KEYS)
    match key:
        case "boolean":
            if not isinstance(v, bool):
                raise Unsupported("malformed boolean literal")
            return Const("bool", v, kind="bool")
        case "string":
            if not isinstance(v, str):
                raise Unsupported("malformed string literal")
            return Const("str", v, kind="str")
        case "null":
            # Lean writes every NULL whose kind it does not know as an `i64`
            # one, so that type says nothing (an outer join's padding is one).
            kind = _type_kinds(v)[1]
            return Const("null", kind=None if kind == "int" else kind)
        case "fp32" | "fp64":
            if isinstance(v, bool):
                raise Unsupported("malformed floating-point literal")
            if isinstance(v, int | float):
                return Const("flt", float(v), kind="float")
            if isinstance(v, str):
                f = Const("str", v).to_float()
                if f is None:
                    raise Unsupported(f"cannot parse double {v}")
                return Const("flt", f, kind="float")
            raise Unsupported("malformed floating-point literal")
        case "decimal":
            return Const("dec", _decode_decimal(_req(v, "value")), _nat_d(v, "scale"))
        case "intervalDayToSecond":
            return Const("int", _interval_micros(v), kind="interval")
        case "intervalCompound" | "intervalYearToMonth":
            months, micros = _interval_lit({"literal": {key: v}}) or (0, 0)
            if months != 0:
                raise Unsupported(
                    "month and year intervals are only supported added to a date or timestamp"
                )
            return Const("int", micros, kind="interval")
        case "precisionTimestamp":
            if _nat_d(v, "precision") != 6:
                raise Unsupported("only microsecond timestamps are supported")
            return Const("int", _int(_req(v, "value")), kind="time")
        case "timestamp":
            return Const("int", _int(v), kind="time")
        case "date":
            return Const("int", _int(v), kind="date")
        case "precisionTime":
            p, value = _nat_d(v, "precision"), _int(_req(v, "value"))
            if p <= 6:
                return Const("int", value * 10 ** (6 - p), kind="tod")
            if value % 10 ** (p - 6):
                raise Unsupported("times finer than microseconds are not supported")
            return Const("int", value // 10 ** (p - 6), kind="tod")
        case "time":
            return Const("int", _int(v), kind="tod")
    return Const("int", _int(v), kind="int")


def _arrow_cast(c: Const, ty: str) -> Const | None:
    if ty.startswith("Timestamp("):
        target = "precisionTimestamp"
    elif ty in ("Float64", "Float32"):
        target = "fp64"
    elif ty == "Date32":
        target = "date"
    elif ty.startswith("Int"):
        target = "i64"
    elif ty == "Utf8":
        target = "string"
    else:
        return None
    try:
        return _cast_const({target: {}}, c)
    except Unsupported:
        return None


def _trunc(f: float) -> float:
    if math.isnan(f) or math.isinf(f):
        return f
    return math.copysign(float(math.floor(f) if f >= 0 else math.ceil(f)), f)


def _fold_call(name: str, cs: list[Const]) -> Const | None:
    """`foldCall`: a function the parser evaluates on constants."""
    match name, cs:
        case "arrow_cast", [c, Const(tag="str", value=ty)]:
            return _arrow_cast(c, ty)
        case "negate", [Const(tag="int") as c]:
            return Const("int", -c.value, kind=c.kind)
        case "negate", [c]:
            f = c.to_float()
            # One zero and one NaN: negating either gives itself.
            return None if f is None else Const("flt", -f if f == f and f != 0 else f, kind="float")
        case "trunc", [c]:
            f = c.to_float()
            return None if f is None else Const("flt", _trunc(f), kind="float")
        case "to_seconds", [c]:
            f = c.to_float()
            us = None if f is None else Const("flt", f * 1000000.0).to_int()
            return None if us is None else Const("int", us, kind="interval")
        case (("to_minutes" | "to_hours" | "to_days"), [c]):
            i = c.to_int()
            unit = {"to_minutes": 60_000_000, "to_hours": 3_600_000_000, "to_days": 86_400_000_000}
            return None if i is None else Const("int", i * unit[name], kind="interval")
        case "normalized_interval", [c]:
            return c
    return None


def _lit(c: Const) -> Lit:
    """`constExpr`."""
    match c.tag:
        case "int":
            return Lit(c.value, c.kind)
        case "flt":
            return Lit(c.value, "float")
        case "str":
            return Lit(c.value, "str")
        case "bool":
            return Lit(c.value, "bool")
        case "null":
            return Lit(None, c.kind)
    raise Unsupported("DECIMAL values are not supported; cast them to DOUBLE")


@dataclass
class _Cols:
    lean: list[LeanKind]
    sql: list[Kind | None]


class _Parser:
    def __init__(self, plan: dict):
        self.fns: dict[int, str] = {}
        for e in _arr(plan, "extensions"):
            f = _field(e, "extensionFunction")
            if f is not None:
                self.fns.setdefault(_nat_d(f, "functionAnchor"), _req(f, "name"))

    def name(self, anchor: int) -> str:
        if anchor not in self.fns:
            raise Unsupported(f"function reference {anchor} is not declared in extensions")
        return self.fns[anchor]

    # Constants

    def const(self, j: Any) -> Const | None:
        """`constOf?`."""
        if (lit := _field(j, "literal")) is not None:
            # Months are not microseconds: `temporal_arith` reads these.
            if (iv := _interval_lit(j)) is not None and iv[0] != 0:
                return None
            return _const_literal(lit)
        if (c := _field(j, "cast")) is not None:
            x = self.const(_req(c, "input"))
            return None if x is None else _cast_const(_req(c, "type"), x)
        if (f := _field(j, "scalarFunction")) is not None:
            name = self.fns.get(_nat_d(f, "functionReference"))
            if name is None:
                return None
            args = [self.const(_req(a, "value")) for a in _arr(f, "arguments")]
            if any(a is None for a in args):
                return None
            return _fold_call(_base_name(name), args)  # type: ignore[arg-type]
        return None

    # Expressions

    def expr(self, j: Any, cols: _Cols) -> Expr:
        """`parseExpr`."""
        if (c := self.const(j)) is not None:
            return _lit(c)
        if _field(j, "literal") is not None:
            raise Unsupported(
                "month and year intervals are only supported added to a date or timestamp"
            )
        key, v = _oneof(
            "expression", j, ("selection", "scalarFunction", "ifThen", "cast", "singularOrList")
        )
        match key:
            case "selection":
                if _field(v, "outerReference") is not None:
                    raise Unsupported("outer references are not supported")
                sf = _req(_req(v, "directReference"), "structField")
                if _field(sf, "child") is not None:
                    raise Unsupported("nested field references are not supported")
                return Field(_nat_d(sf, "field"))
            case "scalarFunction":
                full_name = self.name(_nat_d(v, "functionReference"))
                name = _base_name(full_name)
                arg_js = [_req(a, "value") for a in _arr(v, "arguments")]
                # `array_length(regexp_match(s, p))`: NULL if `p` does not match.
                if name == "array_length" and len(arg_js) == 1:
                    g = _field(arg_js[0], "scalarFunction")
                    inner = None if g is None else self.fns.get(_nat_d(g, "functionReference"))
                    if g is not None and inner is not None and _base_name(inner) == "regexp_match":
                        gargs = [_req(a, "value") for a in _arr(g, "arguments")]
                        if len(gargs) != 2:
                            raise Unsupported("regexp_match with flags is not supported")
                        pat = self.const(gargs[1])
                        if pat is None or pat.tag != "str":
                            raise Unsupported("regular expressions must be constants")
                        return Un("regex_match", self.expr(gargs[0], cols), param=pat.value)
                out_kind = _lean_type_kind(_field(v, "outputType"))
                if (t := self.temporal_arith(name, arg_js, cols, out_kind)) is not None:
                    return t
                if name in _COMPARISONS and any(_calendar_interval(a) for a in arg_js):
                    raise Unsupported(
                        f"{name} with an interval of days or months is not supported: DataFusion "
                        "compares durations with it as (months, days, nanoseconds); write it in "
                        "hours or seconds"
                    )
                parsed = [self.expr(a, cols) for a in arg_js]
                if name == "date_diff" and any(
                    _arg_kind(cols.lean, a, e) != "date"
                    for a, e in zip(arg_js, parsed, strict=True)
                ):
                    raise Unsupported("date_diff takes two dates")
                if name == "date_bin":
                    if len(arg_js) != 3:
                        raise Unsupported("date_bin takes an interval, a timestamp and an origin")
                    iv = _interval_lit(arg_js[0])
                    origin = self.const(arg_js[2])
                    if iv is None or iv[0] != 0 or iv[1] <= 0:
                        raise Unsupported("date_bin needs a constant interval of days or less")
                    if origin is None or origin.tag != "int":
                        raise Unsupported("date_bin needs a constant origin")
                    if lean_expr_kind(parsed[1], cols.lean) != "time":
                        raise Unsupported("date_bin is only supported on timestamps")
                    return Un("bucket", parsed[1], digits=iv[1], origin=origin.value)
                if name in ("strftime", "to_char", "date_format"):
                    first = parsed[0] if parsed else Lit(None, None)
                    if lean_expr_kind(first, cols.lean) != "time":
                        raise Unsupported(f"{name} is only supported on timestamps")
                if name in ("date_part", "datepart", "date_trunc", "datetrunc"):
                    second = parsed[1] if len(parsed) > 1 else Lit(None, None)
                    k = _arg_kind(cols.lean, arg_js[1], second) if len(arg_js) > 1 else "other"
                    if k == "tod":
                        call = _call(name, parsed)
                        clock = ("hour", "minute", "second", "millisecond", "microsecond")
                        if isinstance(call, Un) and call.op == "date_part" and call.param in clock:
                            return call
                        raise Unsupported(
                            f"{name} of a time of day is only supported for its clock"
                        )
                    if k == "date":
                        # The same function of a DATE (days).
                        call = _call(name, parsed)
                        if isinstance(call, Un) and call.op == "date_part":
                            return replace(call, op="day_part")
                        if isinstance(call, Un) and call.op == "date_trunc":
                            if call.param not in ("day", "week", "month", "quarter", "year"):
                                raise Unsupported(
                                    f"date_trunc of a date to a {call.param} is not supported"
                                )
                            return replace(call, op="day_trunc")
                        return call
                    if k != "time":
                        raise Unsupported(f"{name} is only supported on timestamps and dates")

                def keep_int(k: int) -> bool:
                    # `ROUND(x, d)`: the digits stay an integer.
                    return name == "round" and k == 1

                out_ty = _field(v, "outputType")
                # `Parse.wideIntDecimal`: other decimal results are not modelled.
                decimal = isinstance(out_ty, dict) and "decimal" in out_ty
                if decimal and not _wide_int_decimal(out_ty):
                    raise Unsupported(f"{name}: decimal results are not supported")
                out = _lean_type_kind(out_ty)
                floats = (
                    "add", "subtract", "multiply", "divide", "negate", "abs", "power", "floor",
                    "ceil", "round", *DOUBLE_FNS,
                )  # fmt: skip
                has_float = any(lean_expr_kind(e, cols.lean) == "float" for e in parsed)
                float_call = name in floats and (out == "float" or has_float or name in DOUBLE_FNS)
                if name in (*BITWISE, "bitwise_not", "shift_left", "shift_right") and has_float:
                    raise Unsupported(f"{name} is only supported on integers")
                # An integer constant next to a double, or in a double
                # function, stands for that double.
                if has_float or float_call:
                    parsed = [
                        e if keep_int(k) else self._as_double(a, e)
                        for k, (a, e) in enumerate(zip(arg_js, parsed, strict=True))
                    ]
                # DataFusion's simplifier makes `power(x, 0)` a constant 1, even
                # for a NULL `x` (as `Parse.parseExpr`).
                exponent = parsed[1] if name == "power" and len(parsed) == 2 else None
                if isinstance(exponent, Lit) and repr(exponent.value) in ("0", "0.0"):
                    return Lit(1.0, "float") if float_call else Lit(1, "int")
                # Substrait's typed `greatest`/`least` are NULL if any argument is.
                if name in ("greatest", "least") and ":" in full_name:
                    out_e = _call(name, parsed)
                    for a in reversed(parsed):
                        out_e = If(Un("is_null", a), Lit(None, None), out_e)
                    return out_e
                if float_call:
                    # Integer arguments of a double function are converted.
                    parsed = [
                        Un("itof", e)
                        if lean_expr_kind(e, cols.lean) == "int"
                        and not keep_int(k)
                        and not isinstance(e, Lit)
                        else e
                        for k, e in enumerate(parsed)
                    ]
                    return _float_call(name, parsed)
                return _call(name, parsed)
            case "ifThen":
                # A `CASE` without `ELSE` is `ELSE NULL`.
                orelse = _field(v, "else")
                acc = Lit(None, None) if orelse is None else self.expr(orelse, cols)
                for clause in reversed(_arr(v, "ifs")):
                    acc = If(
                        self.expr(_req(clause, "if"), cols),
                        self.expr(_req(clause, "then"), cols),
                        acc,
                    )
                return acc
            case "cast":
                inp = _req(v, "input")
                target = _lean_type_kind(_req(v, "type"))
                # `CAST(d + INTERVAL '1' DAY AS DATE)`: the date arithmetic itself.
                f = _field(inp, "scalarFunction")
                retype = target == "date" and f is not None
                if retype and _lean_type_kind(_field(f, "outputType")) == "time":
                    inp = {"scalarFunction": {**f, "outputType": {"date": {}}}}
                e = self.expr(inp, cols)
                k = lean_expr_kind(e, cols.lean)
                # `Parse.wideIntDecimal`; a duration compared with an interval.
                if k == "int" and _wide_int_decimal(_req(v, "type")):
                    return e
                if k == "time" and _interval_type(_req(v, "type")):
                    return e
                if target == "float" and k == "int":
                    return Un("itof", e)
                # Fails on NaN, ±inf and out-of-range values.
                if target == "int" and k == "float":
                    return Un("ftoi", e)
                if target == "str" and k == "int":
                    return Un("itos", e)
                if target == "date" and k == "time":
                    return Un("to_date", e)
                if target == "tod" and k == "time":
                    return Un("time_of_day", e)
                # Microseconds since 1970-01-01 (arrow's cast of an integer).
                if target == "time" and k == "int":
                    return Un("as_time", e)
                # Fails where the value does not fit (`UnFn.narrow`).
                if target == "int" and k == "int":
                    bits = _int_bits(_req(v, "type"))
                    return Un("narrow", e, digits=bits) if bits < 64 else e
                if target == k and target != "other":
                    return e
                raise Unsupported(f"unsupported cast from {k} to {target}")
            case "singularOrList":
                value = self.expr(_req(v, "value"), cols)
                is_float = lean_expr_kind(value, cols.lean) == "float"
                opts = [
                    self._as_double(o, self.expr(o, cols)) if is_float else self.expr(o, cols)
                    for o in _arr(v, "options")
                ]
                if not opts:
                    return Lit(False, "bool")
                acc: Expr = Bin("eq", value, opts[0])
                for o in opts[1:]:
                    acc = Bin("or", acc, Bin("eq", value, o))
                return acc
        raise Unsupported(f"unsupported expression: {key}")

    def temporal_arith(self, name: str, arg_js: list, cols: _Cols, out: LeanKind) -> Expr | None:
        """`temporalArith`: `x ± interval` of a DATE, or of a timestamp and an
        interval with months."""
        if name not in ("add", "subtract") or len(arg_js) != 2:
            return None
        sub = name == "subtract"
        aj, bj = arg_js
        a = self.expr(aj, cols)
        ka = _arg_kind(cols.lean, aj, a)
        if ka not in ("date", "time"):
            return None
        if ka == "date" and out == "time":
            raise Unsupported("a date plus an interval typed as a timestamp is not supported")
        iv = _interval_lit(bj)
        b = Lit(iv[1], "interval") if iv is not None else self.expr(bj, cols)
        if ka == "date" and _arg_kind(cols.lean, bj, b) == "date":
            raise Unsupported(
                "date - date is not supported (DataFusion compares the duration wrongly); "
                "use date_diff"
            )
        if iv is not None:
            months = -iv[0] if sub else iv[0]
            rest: Expr | None = None if iv[1] == 0 else Lit(iv[1], "interval")
        else:
            months, rest = 0, b
        if ka == "time":
            if months == 0:
                return None
            x = Un("add_months", a, digits=months, param="time")
            return x if rest is None else Bin("sub" if sub else "add", x, rest)
        x = a if months == 0 else Un("add_months", a, digits=months, param="date")
        if rest is None:
            return x
        match rest:
            case Lit(value=int(us)):
                if us % US_PER_DAY:
                    raise Unsupported("a date plus a part of a day is not supported")
                days: Expr = Lit(us // US_PER_DAY, "int")
            case Bin(op="mul", left=n, right=Lit(value=int(us))) if not isinstance(us, bool):
                if us % US_PER_DAY or us == 0:
                    raise Unsupported("a date plus a part of a day is not supported")
                if lean_expr_kind(n, cols.lean) != "int" and _reads_field(n):
                    raise Unsupported(
                        "a date plus an interval is only supported with an integer count of days"
                    )
                n = replace(n, kind="int") if isinstance(n, Lit) else n
                days = n if us == US_PER_DAY else Bin("mul", n, Lit(us // US_PER_DAY, "int"))
            case _:
                raise Unsupported(
                    "a date plus an interval is only supported for constants, or a count of days"
                )
        if sub:
            days = Lit(-days.value, "int") if isinstance(days, Lit) else Un("neg", days)
        return Bin("date_add", x, days)

    def _as_double(self, j: Any, e: Expr) -> Expr:
        c = self.const(j)
        if c is not None and c.tag == "int":
            return Lit(float(c.value), "float")
        return e

    # Windows

    def column(self, j: Any, cols: _Cols, what: str) -> int:
        e = self.expr(j, cols)
        if not isinstance(e, Field):
            raise Unsupported(f"window {what} must be columns")
        return e.index

    def sort_key(self, s: dict, cols: _Cols) -> SortKey:
        col = self.column(_req(s, "expr"), cols, "sort keys")
        d = _field(s, "direction")
        dirs = {
            "SORT_DIRECTION_ASC_NULLS_FIRST": (False, True),
            "SORT_DIRECTION_ASC_NULLS_LAST": (False, False),
            "SORT_DIRECTION_DESC_NULLS_FIRST": (True, True),
            "SORT_DIRECTION_DESC_NULLS_LAST": (True, False),
        }
        if d not in dirs:
            raise Unsupported(f"unsupported sort direction: {'unspecified' if d is None else d}")
        return SortKey(col, *dirs[d])

    def window(self, w: dict, cols: _Cols) -> tuple[tuple[int, ...], tuple[SortKey, ...], WinFn]:
        name = _base_name(self.name(_nat_d(w, "functionReference")))
        part = tuple(self.column(p, cols, "partitions") for p in _arr(w, "partitions"))
        sort = tuple(self.sort_key(s, cols) for s in _arr(w, "sorts"))
        args = [_req(a, "value") for a in _arr(w, "arguments")]
        match name:
            case "row_number":
                if args:
                    raise Unsupported("row_number takes no arguments")
                return part, sort, WinFn("row_number")
            case "lag" | "lead":
                if not args:
                    raise Unsupported(f"{name} needs a column")
                c = self.column(args[0], cols, "function arguments")
                offset = 1
                if len(args) > 1:
                    k = self.const(args[1])
                    if k is None or k.tag != "int":
                        raise Unsupported(f"{name} offsets must be integer constants")
                    if k.value < 0:
                        raise Unsupported(f"negative {name} offset")
                    offset = k.value
                default = Lit(None, None)
                if len(args) > 2:
                    d = self.const(args[2])
                    if d is None:
                        raise Unsupported(f"{name} defaults must be constants")
                    if d.tag == "int" and _get(cols.lean, c) == "float":
                        default = Lit(float(d.value), "float")
                    else:
                        default = _lit(d)
                return part, sort, WinFn(name, c, offset, default)
            case "rank" | "dense_rank" | "percent_rank" | "cume_dist":
                if args:
                    raise Unsupported(f"{name} takes no arguments")
                return part, sort, WinFn(name)
            case "ntile":
                return part, sort, WinFn("ntile", offset=self.positive(args, 0, name))
            case "first_value" | "last_value" | "nth_value":
                if len(args) != (2 if name == "nth_value" else 1):
                    raise Unsupported(f"{name} takes a column")
                c = self.column(args[0], cols, "function arguments")
                n = self.positive(args, 1, name) if name == "nth_value" else 0
                return part, sort, WinFn(name, c, n, frame=self.frame(w, cols, sort))
            case "count" | "sum" | "avg" | "min" | "max":
                # The window's sort keys order the frame, not the aggregate.
                keys = ("functionReference", "arguments", "outputType")
                m = self.measure({"measure": {k: w[k] for k in keys if k in w}}, cols)
                if m.distinct:
                    raise Unsupported("DISTINCT window aggregates are not supported")
                if not _issue_free(m.arg):
                    raise Unsupported(
                        "window aggregates of expressions are not supported; use a column"
                    )
                fr = self.frame(w, cols, sort)
                if m.fn in ("fsum", "avg", "min") and fr.lo != ("unbounded", 0):
                    raise Unsupported(
                        f"{name} over a sliding frame is not supported "
                        "(DataFusion retracts rows wrongly)"
                    )
                return part, sort, WinFn("agg", measure=m, frame=fr)
        raise Unsupported(f"unsupported window function: {name}")

    def positive(self, args: list, i: int, name: str) -> int:
        k = self.const(args[i]) if i < len(args) else None
        if k is None or k.tag != "int" or k.value <= 0:
            raise Unsupported(f"{name} needs a positive constant")
        return k.value

    def frame(self, w: dict, cols: _Cols, sort: tuple[SortKey, ...]) -> Frame:
        """`parseFrame`."""
        bt = _field(w, "boundsType")
        if bt == "BOUNDS_TYPE_ROWS":
            rng = False
        elif bt in (None, "BOUNDS_TYPE_RANGE", "BOUNDS_TYPE_UNSPECIFIED"):
            rng = True
        else:
            raise Unsupported(f"unsupported window bounds type: {bt}")

        def bound(b: Any) -> tuple[str, int]:
            if b is None:
                return ("unbounded", 0)
            key, v = _oneof("frame bound", b, ("unbounded", "currentRow", "preceding", "following"))
            if key == "unbounded":
                return ("unbounded", 0)
            if key == "currentRow":
                return ("preceding", 0)
            k = _int(_field(v, "offset") or 0)
            if k < 0:
                raise Unsupported("negative frame offsets are not supported")
            return (key, k)

        lo, hi = bound(_field(w, "lowerBound")), bound(_field(w, "upperBound"))
        if rng and any(b[0] != "unbounded" and b[1] != 0 for b in (lo, hi)):
            if len(sort) != 1:
                raise Unsupported("RANGE frames with offsets need exactly one sort key")
            if _get(cols.lean, sort[0].col) not in ("int", "time", "date"):
                raise Unsupported(
                    "RANGE frames with offsets need an integer, timestamp or date sort key"
                )
        return Frame(rng, lo, hi)

    def window_project(self, inp: Rel, cols: _Cols, es: list) -> Rel:
        """`parseWindowProject`."""
        n = len(cols.lean)
        parsed: list[tuple[str, Any]] = []
        for e in es:
            w = _field(e, "windowFunction")
            parsed.append(
                ("w", self.window(w, cols)) if w is not None else ("e", self.expr(e, cols))
            )
        groups: list[tuple[tuple[int, ...], tuple[SortKey, ...], list[WinFn]]] = []
        for tag, p in parsed:
            if tag != "w":
                continue
            part, sort, f = p
            for g in groups:
                if g[0] == part and g[1] == sort:
                    g[2].append(f)
                    break
            else:
                groups.append((part, sort, [f]))
        windowed = inp
        for part, sort, fs in groups:
            windowed = Window(windowed, part, sort, tuple(fs))
        width = sum(len(g[2]) for g in groups)

        def column(part: tuple, sort: tuple, f: WinFn, seen: int) -> int:
            off = n
            for p, s, fs in groups:
                if p == part and s == sort:
                    idxs = [i for i, g in enumerate(fs) if g == f]
                    return off + (idxs[seen] if seen < len(idxs) else 0)
                off += len(fs)
            return off

        scalars = [p for tag, p in parsed if tag == "e"]
        mapping: list[int] = []
        seen: list[Any] = []
        j = 0
        for tag, p in parsed:
            if tag == "w":
                part, sort, f = p
                mapping.append(column(part, sort, f, seen.count(p)))
                seen.append(p)
            else:
                mapping.append(n + width + j)
                j += 1
        full = list(range(n)) + mapping
        if not scalars and full == list(range(n + width)):
            return windowed
        core = windowed if not scalars else Project(windowed, tuple(scalars))
        return Emit(core, tuple(full))

    # Relations

    def read(self, r: dict) -> Rel:
        schema = _req(r, "baseSchema")
        st = _field(schema, "struct")
        arity = len(_arr(st, "types")) if st is not None else len(_arr(schema, "names"))
        types = _schema_types(schema)
        sql_kinds = tuple(_type_kinds(t)[1] for t in types) + (None,) * (arity - len(types))
        lean = [_lean_type_kind(t) for t in types]
        key, v = _oneof("read type", r, ("namedTable", "virtualTable"))
        base: Rel
        if key == "namedTable":
            base = Read(
                tuple(_arr(v, "names")), tuple(_arr(schema, "names")), sql_kinds, tuple(lean)
            )
        else:
            if _field(v, "expressions") is not None:
                rows = tuple(
                    tuple(self.expr(e, _Cols([], [])) for e in _arr(row, "fields"))
                    for row in _arr(v, "expressions")
                )
            else:
                rows = tuple(
                    tuple(_lit(_const_literal(e)) for e in _arr(row, "fields"))
                    for row in _arr(v, "values")
                )
            base = Values(arity, rows, _values_kinds(rows, sql_kinds), tuple(lean))
        cond = _field(r, "filter")
        if cond is not None:
            base = Filter(base, self.expr(cond, _Cols(lean, kinds(base))))
        mask = _field(r, "projection")
        if mask is not None:
            items = _arr(_req(mask, "select"), "structItems")
            if any(_field(i, "child") is not None for i in items):
                raise Unsupported("nested projection masks are not supported")
            base = Emit(base, tuple(_nat_d(i, "field") for i in items))
        return base

    def cols(self, r: Rel) -> _Cols:
        return _Cols(lean_kinds(r), kinds(r))

    def rel(self, j: dict) -> Rel:
        """`parseRel`."""
        kind, r = _oneof(
            "relation",
            j,
            ("read", "filter", "project", "cross", "join", "fetch", "set", "sort", "aggregate"),
        )
        core: Rel
        match kind:
            case "read":
                core = self.read(r)
            case "filter":
                inp = self.rel(_req(r, "input"))
                cols = self.cols(inp)
                # `x IN (subquery)` conjuncts become semi joins; the rest stays a filter.
                base: Rel = inp
                rest: list[Expr] = []
                for c in self.conjuncts(_req(r, "condition")):
                    sub = _field(c, "subquery")
                    ip = _field(sub, "inPredicate") if sub is not None else None
                    if ip is None:
                        rest.append(self.expr(c, cols))
                        continue
                    needles = _arr(ip, "needles")
                    if len(needles) != 1:
                        raise Unsupported("IN with several needles is not supported")
                    needle = self.expr(needles[0], cols)
                    hay = self.rel(_req(ip, "haystack"))
                    if len(lean_kinds(hay)) != 1:
                        raise Unsupported("IN subquery must return one column")
                    base = Semi(base, hay, False, Bin("eq", needle, Field(len(cols.lean))))
                if not rest:
                    core = base
                else:
                    cond = rest[0]
                    for e in rest[1:]:
                        cond = Bin("and", cond, e)
                    core = Filter(base, cond)
            case "project":
                inp = self.rel(_req(r, "input"))
                cols = self.cols(inp)
                ejs = _arr(r, "expressions")
                if any(_field(e, "windowFunction") is not None for e in ejs):
                    core = self.window_project(inp, cols, ejs)
                else:
                    es = tuple(self.expr(e, cols) for e in ejs)
                    core = Project(inp, es) if es else inp
            case "cross":
                core = Cross(self.rel(_req(r, "left")), self.rel(_req(r, "right")))
            case "join":
                t = _field(r, "type")
                if _field(r, "postJoinFilter") is not None:
                    raise Unsupported("JoinRel.postJoinFilter is not supported")
                left, right = self.rel(_req(r, "left")), self.rel(_req(r, "right"))
                lc, rc = self.cols(left), self.cols(right)
                n, m = len(lc.lean), len(rc.lean)
                cols = _Cols(lc.lean + rc.lean, lc.sql + rc.sql)
                e = _field(r, "expression")
                on = Lit(True, "bool") if e is None else self.expr(e, cols)
                # The condition with the sides swapped, and `b`'s columns then
                # `a`'s put back in order.
                swapped = _map_fields(on, lambda i: m + i if i < n else i - n)
                back = tuple([m + i for i in range(n)] + list(range(m)))
                match t:
                    case "JOIN_TYPE_INNER":
                        core = Join(left, right, "inner", on)
                    case "JOIN_TYPE_LEFT":
                        core = Join(left, right, "left", on)
                    case "JOIN_TYPE_RIGHT":
                        core = Emit(Join(right, left, "left", swapped), back)
                    case "JOIN_TYPE_LEFT_SEMI":
                        core = Semi(left, right, False, on)
                    case "JOIN_TYPE_LEFT_ANTI":
                        core = Semi(left, right, True, on)
                    case "JOIN_TYPE_RIGHT_SEMI":
                        core = Semi(right, left, False, swapped)
                    case "JOIN_TYPE_RIGHT_ANTI":
                        core = Semi(right, left, True, swapped)
                    case "JOIN_TYPE_OUTER":
                        # The left join, plus the right rows nothing matches, padded.
                        pad = Project(Semi(right, left, True, swapped), (Lit(None, None),) * n)
                        core = UnionAll(Join(left, right, "left", on), Emit(pad, back))
                    case _:
                        raise Unsupported(
                            f"unsupported join type: {'unspecified' if t is None else t}"
                        )
            case "fetch":
                offset = self.fetch_int(r, "offset")
                if offset is not None and offset < 0:
                    raise Unsupported("negative FetchRel offset")
                count = self.fetch_int(r, "count")
                core = Fetch(
                    self.rel(_req(r, "input")),
                    offset or 0,
                    None if count is None or count < 0 else count,
                )
            case "sort":
                inp = self.rel(_req(r, "input"))
                cols = self.cols(inp)
                core = OrderBy(inp, tuple(self.sort_key(k, cols) for k in _arr(r, "sorts")))
            case "aggregate":
                core = self.aggregate(r)
            case _:
                inputs = [self.rel(i) for i in _arr(r, "inputs")]
                if not inputs:
                    raise Unsupported("SetRel without inputs")
                core = inputs[0]
                for i in inputs[1:]:
                    core = UnionAll(core, i)
                op = _field(r, "op")
                if op == "SET_OP_UNION_DISTINCT":
                    core = Distinct(core)
                elif op != "SET_OP_UNION_ALL":
                    raise Unsupported(
                        f"unsupported set operation: {'unspecified' if op is None else op}"
                    )
        common = _field(r, "common")
        emit = _field(common, "emit") if common is not None else None
        if emit is not None:
            m = [_nat(i) for i in _arr(emit, "outputMapping")]
            if isinstance(core, Emit):
                return Emit(
                    core.input, tuple(core.mapping[i] if i < len(core.mapping) else 0 for i in m)
                )
            return Emit(core, tuple(m))
        return core

    def aggregate(self, r: dict) -> Rel:
        """`AggregateRel`, as `parseRel` reads it: `DISTINCT` when there are no
        measures and the groups are columns, else `Rel.aggregate`."""
        inp = self.rel(_req(r, "input"))
        cols = self.cols(inp)
        measures = _arr(r, "measures")
        groupings = _arr(r, "groupings")
        groups: list[Expr] | None
        if not groupings:
            groups = []
        elif len(groupings) > 1:
            raise Unsupported("grouping sets are not supported")
        else:
            g = groupings[0]
            refs, exprs = _field(g, "expressionReferences"), _field(g, "groupingExpressions")
            if refs is None and exprs is None:
                # DataFusion writes `DISTINCT` as one empty grouping (which its
                # own consumer rejects); without measures it can only mean all columns.
                groups = None if not measures else []
            else:
                top = _arr(r, "groupingExpressions")
                if refs is not None:
                    js = []
                    for k in _arr(g, "expressionReferences"):
                        k = _nat(k)
                        if k >= len(top):
                            raise Unsupported(f"grouping expression {k} does not exist")
                        js.append(top[k])
                else:
                    js = _arr(g, "groupingExpressions")
                groups = [self.expr(e, cols) for e in js]
        if groups is None:
            return Distinct(inp)
        if not measures:
            if not groups:
                raise Unsupported("an aggregate without groupings needs measures")
            if all(isinstance(e, Field) for e in groups):
                keys = tuple(e.index for e in groups if isinstance(e, Field))
                if keys == tuple(range(len(cols.lean))):
                    return Distinct(inp)
                return Distinct(Emit(inp, keys))
        return Aggregate(inp, tuple(groups), tuple(self.measure(m, cols) for m in measures))

    def measure(self, mj: dict, cols: _Cols) -> Measure:
        """`parseMeasure`. `AVG` of integers averages their conversions to
        double; `COUNT(*)` may come with no argument."""
        m = _req(mj, "measure")
        name = _base_name(self.name(_nat_d(m, "functionReference")))
        if _arr(m, "sorts"):
            raise Unsupported(f"ordered aggregates are not supported: {name}")
        inv = _field(m, "invocation")
        if inv not in (None, "AGGREGATION_INVOCATION_ALL", "AGGREGATION_INVOCATION_UNSPECIFIED",
                       "AGGREGATION_INVOCATION_DISTINCT"):  # fmt: skip
            raise Unsupported(f"unsupported aggregate invocation: {inv}")
        f = _field(mj, "filter")
        cond = None if f is None else self.expr(f, cols)
        args = [_req(a, "value") for a in _arr(m, "arguments")]
        if len(args) == 1:
            arg = self.expr(args[0], cols)
        elif not args and name == "count":
            arg = Lit(1, "int")
        elif not args:
            raise Unsupported(f"{name} needs an argument")
        else:
            raise Unsupported(f"{name} takes one argument")
        k = lean_expr_kind(arg, cols.lean)
        # `AVG` is a double; Calcite's `AVG` of integers (`avg:i64`) is not.
        if name == "avg" and "outputType" in m and _lean_type_kind(m["outputType"]) != "float":
            raise Unsupported("avg with a non-double result is not supported")
        fn: Literal["count", "sum", "fsum", "avg", "min", "max"]
        match name, k:
            case "count", _:
                fn = "count"
            case "sum", "int":
                fn = "sum"
            case "sum", "float":
                fn = "fsum"
            case "avg", "int":
                fn, arg = "avg", Un("itof", arg)
            case "avg", "float":
                fn = "avg"
            case (("min" | "max"), "float"):
                raise Unsupported(f"{name} of doubles is not supported")
            case (("min" | "max"), ("int" | "str" | "bool" | "time" | "date")):
                fn = name
            case (("min" | "max" | "sum" | "avg"), _):
                raise Unsupported(f"{name} of this type is not supported")
            case _:
                raise Unsupported(f"unsupported aggregate function: {name}")
        return Measure(fn, arg, inv == "AGGREGATION_INVOCATION_DISTINCT", cond)

    def conjuncts(self, j: Any) -> list[Any]:
        """The conjuncts of a condition, splitting top-level `and` calls."""
        f = _field(j, "scalarFunction")
        if f is not None:
            name = self.fns.get(_nat_d(f, "functionReference"))
            if name is not None and _base_name(name) == "and":
                return [c for a in _arr(f, "arguments") for c in self.conjuncts(_req(a, "value"))]
        return [j]

    def fetch_int(self, r: dict, key: str) -> int | None:
        e = _field(r, key + "Expr")
        if e is not None:
            c = self.const(e)
            if c is not None and c.tag == "int":
                return c.value
            if c is not None and c.tag == "null":
                return None
            raise Unsupported(f"FetchRel.{key}Expr must be an integer constant")
        v = _field(r, key)
        return None if v is None else _int(v)


def _values_kinds(rows: tuple, schema: tuple[Kind | None, ...]) -> tuple[Kind | None, ...]:
    """Column kinds of a virtual table: what its constants are, else what its
    `baseSchema` says (Lean ignores both, and writes placeholder `i64` types)."""
    out = []
    for j, k in enumerate(schema):
        # NULLs say nothing: Lean writes every one as an `i64` NULL.
        values = [row[j] for row in rows if j < len(row)]
        nonnull = [e for e in values if not (isinstance(e, Lit) and e.value is None)]
        seen = {expr_kind(e, []) for e in nonnull} - {None}
        if len(seen) > 1:
            raise Unsupported(f"virtual table column {j} mixes {sorted(seen)}")  # type: ignore[type-var]
        out.append(seen.pop() if seen else k)
    return tuple(out)


def _map_fields(e: Expr, f: Callable[[int], int]) -> Expr:
    match e:
        case Lit():
            return e
        case Field(index=i):
            return Field(f(i))
        case Un(arg=a):
            return replace(e, arg=_map_fields(a, f))
        case Bin(left=a, right=b):
            return replace(e, left=_map_fields(a, f), right=_map_fields(b, f))
        case If(cond=c, then=t, orelse=o):
            return If(_map_fields(c, f), _map_fields(t, f), _map_fields(o, f))


US_PER_DAY = 86_400_000_000


def _reads_field(e: Expr) -> bool:
    match e:
        case Field():
            return True
        case Un(arg=a):
            return _reads_field(a)
        case Bin(left=a, right=b):
            return _reads_field(a) or _reads_field(b)
        case If(cond=c, then=t, orelse=o):
            return _reads_field(c) or _reads_field(t) or _reads_field(o)
    return False


def _arg_kind(cols: list[LeanKind], j: Any, e: Expr) -> LeanKind:
    """`argKind`: a literal's kind is its type's (a date literal is a date)."""
    if _reads_field(e):
        return lean_expr_kind(e, cols)
    lit = _field(j, "literal")
    if lit is not None:
        if _field(lit, "date") is not None:
            return "date"
        if _field(lit, "precisionTimestamp") is not None or _field(lit, "timestamp") is not None:
            return "time"
        if _field(lit, "precisionTime") is not None or _field(lit, "time") is not None:
            return "tod"
    # A constant cast (`DATE '2024-01-31'` is a cast of a string).
    if (c := _field(j, "cast")) is not None:
        k = _lean_type_kind(_field(c, "type"))
        if k in ("date", "time"):
            return k
    return "other"


def _call(name: str, args: list[Expr]) -> Expr:
    """`mkCall`."""
    match name, args:
        case "not", [a]:
            return Un("not", a)
        case "is_null", [a]:
            return Un("is_null", a)
        case "is_not_null", [a]:
            return Un("not", Un("is_null", a))
        case (("negate" | "subtract"), [a]):
            return Un("neg", a)
        case "add", [a, b]:
            return Bin("add", a, b)
        case "subtract", [a, b]:
            return Bin("sub", a, b)
        case "multiply", [a, b]:
            return Bin("mul", a, b)
        case "equal", [a, b]:
            return Bin("eq", a, b)
        case "not_equal", [a, b]:
            return Un("not", Bin("eq", a, b))
        case "lt", [a, b]:
            return Bin("lt", a, b)
        case "gt", [a, b]:
            return Bin("lt", b, a)
        case "lte", [a, b]:
            return Un("not", Bin("lt", b, a))
        case "gte", [a, b]:
            return Un("not", Bin("lt", a, b))
        case "normalized_interval", [a]:
            return a
        case (("is_nan" | "isnan"), [a]):
            return Bin("eq", a, Lit(math.nan, "float"))
        # `nanvl(x, NaN)` is `x` with one NaN, and `x + 0.0` is `x` with one
        # zero: Lean's `canonical`, read back as `Parse.mkCall` reads it.
        case "nanvl", [a, Lit(value=float(v))] if math.isnan(v):
            match a:
                case Bin(op="fadd", left=x, right=Lit(value=0 | 0.0)):
                    return x
            return a
        case (("and" | "or"), [a, *rest]):
            for b in rest:
                a = Bin(name, a, b)  # type: ignore[arg-type]
            return a
        case "coalesce", [a, *rest]:
            return _coalesce(a, rest)
        case "nullif", [a, b]:
            return If(Bin("eq", a, b), Lit(None, None), a)
        case (("greatest" | "greatest_skip_null"), [a, *rest]):
            for b in rest:
                a = _pick(lambda x, y: Bin("lt", x, y), a, b)
            return a
        case (("least" | "least_skip_null"), [a, *rest]):
            for b in rest:
                a = _pick(lambda x, y: Bin("lt", y, x), a, b)
            return a
        case "abs", [a]:
            return If(Bin("lt", a, Lit(0, "int")), Un("neg", a), a)
        # Integer division and remainder truncate; doubles go to `_float_call`.
        case "divide", [a, b]:
            return Bin("idiv", a, b)
        case "modulus", [a, b]:
            return Bin("imod", a, b)
        case "power", [a, b]:
            return Bin("ipow", a, b)
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
        # Bitwise operations (`SubstraitLean/Numeric.lean`); `NOT x` is `x XOR -1`.
        case "bitwise_not", [a]:
            return Bin("bit", a, Lit(-1, "int"), param="bitwise_xor")
        case "shift_left", [a, b]:
            return Bin("bit", a, b, param="bitwise_shift_left")
        case "shift_right", [a, b]:
            return Bin("bit", a, b, param="bitwise_shift_right")
        case _, [a, b] if name in BITWISE:
            return Bin("bit", a, b, param=name)
        case "regexp_match", _:
            raise Unsupported("regexp_match is only supported as array_length(regexp_match(s, p))")
        # Timestamps (`SubstraitLean/Time.lean`).
        case (("date_part" | "datepart"), [Lit(value=str(part)), a]):
            if part.lower() not in DATE_PARTS:
                raise Unsupported(f"unsupported date part '{part}'")
            return Un("date_part", a, param=part.lower())
        case (("date_trunc" | "datetrunc"), [Lit(value=str(unit)), a]):
            if unit.lower() not in TIME_UNITS:
                raise Unsupported(f"unsupported date_trunc unit '{unit}'")
            return Un("date_trunc", a, param=unit.lower())
        case (("strftime" | "to_char" | "date_format"), [a, Lit(value=str(fmt))]):
            if parse_format(fmt) is None:
                raise Unsupported(f"strftime format '{fmt}' is not supported")
            return Un("strftime", a, param=fmt)
        # sverify's own: the days from `e` to `d`.
        case "date_diff", [d, e]:
            return Bin("date_diff", d, e)
    raise Unsupported(f"unsupported function {name}/{len(args)}")


def parse_format(fmt: str) -> list[str] | None:
    """`Time.parseFormat`: text characters and `%` directives (`%Y`, …)."""
    out, i = [], 0
    while i < len(fmt):
        if fmt[i] != "%":
            out.append(fmt[i])
            i += 1
        elif i + 1 < len(fmt) and fmt[i + 1] in "YmdHMSjFT%":
            out.append(fmt[i : i + 2])
            i += 2
        else:
            return None
    return out


#: `Time.DatePart.name` and `Time.TimeUnit.name`.
DATE_PARTS = (
    "year", "quarter", "month", "week", "day", "hour", "minute", "second", "millisecond",
    "microsecond", "dow", "doy",
)  # fmt: skip
TIME_UNITS = (
    "microsecond", "millisecond", "second", "minute", "hour", "day", "week", "month", "quarter",
    "year",
)  # fmt: skip


def _coalesce(a: Expr, rest: list[Expr]) -> Expr:
    if not rest:
        return a
    return If(Un("not", Un("is_null", a)), a, _coalesce(rest[0], rest[1:]))


def _pick(better: Callable[[Expr, Expr], Expr], a: Expr, b: Expr) -> Expr:
    return If(Un("is_null", a), b, If(Un("is_null", b), a, If(better(a, b), b, a)))


def _float_call(name: str, args: list[Expr]) -> Expr:
    """`mkFloatCall`."""
    match name, args:
        case "add", [a, b]:
            return Bin("fadd", a, b)
        case "subtract", [a, b]:
            return Bin("fsub", a, b)
        case "multiply", [a, b]:
            return Bin("fmul", a, b)
        case "divide", [a, b]:
            return Bin("fdiv", a, b)
        case (("subtract" | "negate"), [a]):
            return Un("fneg", a)
        case "abs", [a]:
            return If(Bin("lt", a, Lit(0.0, "float")), Un("fneg", a), a)
        case "power", [a, b]:
            return Bin("fpow", a, b)
        case "floor", [a]:
            return Un("ffloor", a)
        case "ceil", [a]:
            return Un("fceil", a)
        case "round", [a]:
            return Un("fround", a)
        case "round", [a, Lit(value=int(d), kind="int")] if not isinstance(d, bool):
            return Un("fround", a) if d == 0 else Un("froundTo", a, d)
        case "atan2", [y, x]:
            return Bin("fatan2", y, x)
        case "logb", [x, b]:
            return Bin("flogb", x, b)
        case _, [a] if name in FMATH:
            return Un("fmath", a, param=name)
    raise Unsupported(f"unsupported double function {name}/{len(args)}")


@dataclass
class Plan:
    root: Rel
    names: list[str]


def parse_plan(plan: dict) -> Plan:
    """Read a Substrait JSON plan (as a dict) into the model, as `parsePlan` does."""
    p = _Parser(plan)
    root = next((_field(r, "root") for r in _arr(plan, "relations") if _field(r, "root")), None)
    if root is None:
        raise Unsupported("plan has no root relation")
    rel = p.rel(_req(root, "input"))
    names = _arr(root, "names")
    if not all(isinstance(n, str) for n in names):
        raise Unsupported("root names must be strings")
    return Plan(rel, names)


# --------------------------------------------------------------------------
# Writing SQL


def arity(r: Rel) -> int:
    return len(kinds(r))


def numbers_copies(w: Window) -> bool:
    """Is `w` `ROW_NUMBER() OVER (PARTITION BY` every column`)`? It numbers the
    copies of each row, and as a bag that does not depend on the row order
    (the copies are equal)."""
    return (
        not w.sort
        and all(f.fn == "row_number" for f in w.fns)
        and set(w.part) == set(range(arity(w.input)))
    )


def order_matters(r: Rel) -> bool:
    """Does the result's row order matter (a FETCH, a window or a sort anywhere
    the order reaches the result)?"""
    match r:
        case Window(input=i) if numbers_copies(r):
            return order_matters(i)
        case Fetch() | Window() | OrderBy():
            return True
        case Read() | Values():
            return False
        case (
            Filter(input=i) | Project(input=i) | Emit(input=i) | Distinct(input=i)
            | Aggregate(input=i)
        ):  # fmt: skip
            return order_matters(i)
        case Semi(left=a):
            return order_matters(a)
        case Cross(left=a, right=b) | Join(left=a, right=b) | UnionAll(left=a, right=b):
            return order_matters(a) or order_matters(b)


ORD = "o"


@dataclass
class _Writer:
    d: Dialect
    tie_free: bool = False
    n: int = 0

    def alias(self) -> str:
        self.n += 1
        return f"s{self.n}"

    def c(self, i: int) -> str:
        return self.d.quote(f"c{i}")

    def ref(self, alias: str, col: str) -> str:
        return f"{alias}.{col}"

    def ordinal(self, alias: str) -> str:
        return self.ref(alias, self.d.quote(ORD))

    def select(self, items: list[str], from_: str, rest: str = "") -> str:
        return f"SELECT {', '.join(items)} FROM {from_}" + (f" {rest}" if rest else "")

    def passthrough(self, alias: str, n: int, ordered: bool) -> list[str]:
        items = [f"{self.ref(alias, self.c(i))} AS {self.c(i)}" for i in range(n)]
        if ordered:
            items.append(f"{self.ordinal(alias)} AS {self.d.quote(ORD)}")
        return items

    def order_by(self, keys: list[str]) -> str:
        return self.d.over([], keys)

    def asc(self, x: str, nulls_first: bool = False) -> str:
        """An ascending key on an ordinal or tag (an integer)."""
        return self.d.sort_key(x, False, nulls_first, "int")

    # Relations: each returns a SELECT with columns c0… (and `o` when ordered).

    def rel(self, r: Rel, ordered: bool) -> str:
        d = self.d
        n = arity(r)
        if n == 0:
            raise Unsupported("relations without columns have no SQL form")
        match r:
            case Read(name=name, columns=columns):
                if len(columns) != n:
                    raise Unsupported(
                        f"table {'.'.join(name)} needs one name per column in its baseSchema"
                    )
                # A table's `-0.0` is the model's one zero.
                items = [
                    f"{d.canon(d.quote(col)) if k == 'float' else d.quote(col)} AS {self.c(i)}"
                    for i, (col, k) in enumerate(zip(columns, r.kinds, strict=True))
                ]
                if ordered:
                    items.append(f"{d.row_ordinal()} AS {d.quote(ORD)}")
                return self.select(items, ".".join(d.quote(p) for p in name))
            case Values(rows=rows, kinds=ks):
                cols = [self.c(i) for i in range(n)] + ([d.quote(ORD)] if ordered else [])
                for row in rows:
                    if len(row) != n:
                        raise Unsupported(
                            f"a virtual table row has {len(row)} fields, expected {n}"
                        )
                if not rows:
                    items = [f"{d.null(k)} AS {self.c(i)}" for i, k in enumerate(ks)]
                    if ordered:
                        items.append(f"{d.null('int')} AS {d.quote(ORD)}")
                    return f"SELECT {', '.join(items)} WHERE FALSE"
                sql_rows = []
                for idx, row in enumerate(rows):
                    vals = [
                        self.expr(e, lambda i: _no_fields(), [], k)
                        for e, k in zip(row, ks, strict=True)
                    ]
                    sql_rows.append(vals + ([d.int_lit(idx)] if ordered else []))
                a = "v"
                return self.select(
                    [f"{self.ref(a, c)} AS {c}" for c in cols], d.values(sql_rows, cols)
                )
            case Filter(input=i, cond=cond):
                a = self.alias()
                ks = kinds(i)
                self.check_refs(cond, len(ks))
                where = d.is_true(self.expr(cond, lambda j: self.ref(a, self.c(j)), ks, "bool"))
                return self.select(
                    self.passthrough(a, n, ordered),
                    d.subquery(self.rel(i, ordered), a),
                    f"WHERE {where}",
                )
            case Project(input=i, exprs=es):
                a = self.alias()
                ks = kinds(i)
                m = len(ks)
                items = [f"{self.ref(a, self.c(j))} AS {self.c(j)}" for j in range(m)]
                for j, e in enumerate(es):
                    self.check_refs(e, m)
                    sql = self.expr(e, lambda x: self.ref(a, self.c(x)), ks, expr_kind(e, ks))
                    items.append(f"{sql} AS {self.c(m + j)}")
                if ordered:
                    items.append(f"{self.ordinal(a)} AS {d.quote(ORD)}")
                return self.select(items, d.subquery(self.rel(i, ordered), a))
            case Emit(input=i, mapping=mapping):
                a = self.alias()
                m = arity(i)
                if any(j >= m for j in mapping):
                    raise Unsupported(f"emit refers to a column beyond the input's {m}")
                items = [f"{self.ref(a, self.c(j))} AS {self.c(k)}" for k, j in enumerate(mapping)]
                if ordered:
                    items.append(f"{self.ordinal(a)} AS {d.quote(ORD)}")
                return self.select(items, d.subquery(self.rel(i, ordered), a))
            case Cross(left=left, right=right) | Join(left=left, right=right):
                la, ra = self.alias(), self.alias()
                nl = arity(left)
                items = [f"{self.ref(la, self.c(j))} AS {self.c(j)}" for j in range(nl)]
                items += [f"{self.ref(ra, self.c(j))} AS {self.c(nl + j)}" for j in range(n - nl)]
                if ordered:
                    # Left-major, and a left join's unmatched row (no right ordinal) in place.
                    keys = [
                        self.asc(self.ordinal(la)),
                        self.asc(self.ordinal(ra), nulls_first=True),
                    ]
                    items.append(f"{d.row_number(self.order_by(keys))} AS {d.quote(ORD)}")
                lsub = d.subquery(self.rel(left, ordered), la)
                rsub = d.subquery(self.rel(right, ordered), ra)
                if isinstance(r, Cross):
                    return self.select(items, d.cross_join(lsub, rsub))
                ks = kinds(left) + kinds(right)
                self.check_refs(r.on, n)

                def side(j: int) -> str:
                    return self.ref(la, self.c(j)) if j < nl else self.ref(ra, self.c(j - nl))

                on = self.expr(r.on, side, ks, "bool")
                join = "INNER JOIN" if r.type == "inner" else "LEFT JOIN"
                return self.select(items, f"{lsub} {join} {rsub} ON {on}")
            case Fetch(input=i, offset=off, count=cnt):
                a = self.alias()
                rest = f"ORDER BY {self.asc(self.ordinal(a))}"
                if lo := d.limit_offset(off, cnt):
                    rest += " " + lo
                return self.select(
                    self.passthrough(a, n, ordered), d.subquery(self.rel(i, True), a), rest
                )
            case UnionAll(left=left, right=right):
                if arity(left) != arity(right):
                    raise Unsupported("UNION ALL inputs have different numbers of columns")
                if not ordered:
                    branches = []
                    for b in (left, right):
                        a = self.alias()
                        branches.append(
                            self.select(
                                self.passthrough(a, n, False), d.subquery(self.rel(b, False), a)
                            )
                        )
                    return d.union_all(*branches)
                branch = d.quote("b")
                branches = []
                for tag, b in enumerate((left, right)):
                    a = self.alias()
                    items = self.passthrough(a, n, True) + [f"{d.int_lit(tag)} AS {branch}"]
                    branches.append(self.select(items, d.subquery(self.rel(b, True), a)))
                u = self.alias()
                keys = [self.asc(self.ref(u, branch)), self.asc(self.ordinal(u))]
                items = self.passthrough(u, n, False) + [
                    f"{d.row_number(self.order_by(keys))} AS {d.quote(ORD)}"
                ]
                return self.select(items, d.subquery(d.union_all(*branches), u))
            case Window(input=i, part=part, sort=sort, fns=fns):
                return self.window(i, part, sort, fns, ordered)
            case Semi(left=left, right=right, anti=anti, on=on):
                # A correlated `EXISTS`: true when the condition is TRUE for
                # some right row (`hasMatch`); the left rows keep their order.
                la, ra = self.alias(), self.alias()
                nl = arity(left)
                self.check_refs(on, nl + arity(right))

                def side(j: int) -> str:
                    return self.ref(la, self.c(j)) if j < nl else self.ref(ra, self.c(j - nl))

                cond = d.is_true(self.expr(on, side, kinds(left) + kinds(right), "bool"))
                rsub = d.subquery(self.rel(right, False), ra)
                exists = f"{'NOT ' if anti else ''}EXISTS (SELECT 1 FROM {rsub} WHERE {cond})"
                return self.select(
                    self.passthrough(la, n, ordered),
                    d.subquery(self.rel(left, ordered), la),
                    f"WHERE {exists}",
                )
            case OrderBy(input=i, keys=sort):
                # A stable sort: ties keep their input order, by its ordinal.
                a = self.alias()
                ks = kinds(i)
                if any(k.col >= n for k in sort):
                    raise Unsupported("a sort key refers to a column beyond its input")
                keys = self.sort_keys(a, sort, ks)
                items = self.passthrough(a, n, False)
                if ordered:
                    if not keys:
                        items.append(f"{self.ordinal(a)} AS {d.quote(ORD)}")
                    else:
                        items.append(f"{d.row_number(self.order_by(keys))} AS {d.quote(ORD)}")
                needs = ordered and (not self.tie_free or not keys)
                return self.select(items, d.subquery(self.rel(i, needs), a))
            case Distinct(input=i):
                return self.distinct(i, ordered)
            case Aggregate(input=i, groups=gs, measures=ms):
                return self.aggregate(i, gs, ms, ordered)
        raise Unsupported(f"unsupported relation {type(r).__name__}")

    def aggregate(
        self, i: Rel, groups: Sequence[Expr], measures: Sequence[Measure], ordered: bool
    ) -> str:
        """`aggregateEval`. Three steps: the grouping expressions and each
        measure's argument (NULL on rows its filter drops) on every input row;
        for `DISTINCT` measures, the argument only on the first row of each
        value in its group; then `GROUP BY` the groups, as `Value`s. Groups
        come in order of their first row."""
        d = self.d
        ks = kinds(i)
        m = len(ks)
        for e in [*groups, *(x for ms in measures for x in (ms.arg, ms.filter) if x is not None)]:
            self.check_refs(e, m)
        # Double sums add in Lean's list order, which needs the ordinal.
        sums = any(ms.fn in ("fsum", "avg") for ms in measures)
        needs = ordered or sums
        a = self.alias()

        def ref(j: int) -> str:
            return self.ref(a, self.c(j))

        g_cols = [d.quote(f"g{k}") for k in range(len(groups))]
        m_cols = [d.quote(f"m{k}") for k in range(len(measures))]
        # A DISTINCT measure's argument on the first row of each of its values.
        d_cols = [d.quote(f"d{k}") for k in range(len(measures))]
        g_kinds = [expr_kind(g, ks) for g in groups]
        items = [
            f"{self.expr(g, ref, ks, k)} AS {c}"
            for g, k, c in zip(groups, g_kinds, g_cols, strict=True)
        ]
        for ms, c in zip(measures, m_cols, strict=True):
            k = expr_kind(ms.arg, ks)
            x = self.expr(ms.arg, ref, ks, k)
            if ms.filter is not None:
                keep = d.is_true(self.expr(ms.filter, ref, ks, "bool"))
                x = d.case_when(keep, x, d.null(k))
            items.append(f"{x} AS {c}")
        if needs:
            items.append(f"{self.ordinal(a)} AS {d.quote(ORD)}")
        level = self.select(items, d.subquery(self.rel(i, needs), a))
        b = self.alias()

        def col(c: str) -> str:
            return self.ref(b, c)

        keys = [col(c) for c in g_cols]
        if any(ms.distinct for ms in measures):
            # The first row of each value of a DISTINCT measure's argument.
            items = [f"{col(c)} AS {c}" for c in g_cols + m_cols]
            if needs:
                items.append(f"{self.ordinal(b)} AS {d.quote(ORD)}")
            for ms, c, dc in zip(measures, m_cols, d_cols, strict=True):
                if not ms.distinct:
                    continue
                part = [*keys, col(c)]
                order = [self.asc(self.ordinal(b))] if needs else part
                first = f"{d.row_number(d.over(part, order))} = {d.int_lit(1)}"
                value = d.case_when(first, col(c), d.null(expr_kind(ms.arg, ks)))
                items.append(f"{value} AS {dc}")
            level = self.select(items, d.subquery(level, b))
            b = self.alias()
            keys = [col(c) for c in g_cols]
        out = [f"{col(c)} AS {self.c(i)}" for i, c in enumerate(g_cols)]
        for k, ms in enumerate(measures):
            v = col(d_cols[k] if ms.distinct else m_cols[k])
            sql = self.measure(ms, v, expr_kind(ms.arg, ks), self.ordinal(b))
            out.append(f"{sql} AS {self.c(len(groups) + k)}")
        if ordered:
            out.append(f"COALESCE(MIN({self.ordinal(b)}), {d.int_lit(0)}) AS {d.quote(ORD)}")
        rest = f"GROUP BY {', '.join(keys)}" if keys else ""
        return self.select(out, d.subquery(level, b), rest)

    def measure(self, m: Measure, v: str, kind: Kind | None, o: str) -> str:
        """`Measure.eval` of the column `v` (NULL where the measure skips a row)."""
        d = self.d
        match m.fn:
            case "count":
                return f"COUNT({v})"
            case "sum":
                return d.int_sum(v)
            case "fsum" | "avg":
                total = d.float_sum(v, o)
                if m.fn == "avg":
                    total = d.canon(d.float_div(total, d.int_to_float(f"COUNT({v})")))
                return d.case_when(f"COUNT({v}) = {d.int_lit(0)}", d.null("float"), total)
        # `Value.le`: strings by code point (no collation), FALSE < TRUE.
        f = "MIN" if m.fn == "min" else "MAX"
        if kind == "bool":
            as_int = d.case_when(v, d.int_lit(1), d.int_lit(0))
            return f"({f}({d.case_when(f'{v} IS NULL', d.null('int'), as_int)}) = {d.int_lit(1)})"
        return f"{f}({v})"

    def sort_keys(self, a: str, sort: Sequence[SortKey], ks: list[Kind | None]) -> list[str]:
        """ORDER BY keys for `sortLe sort` over subquery `a`, ties broken by its
        ordinal (Lean's merge sort is stable) unless the caller promised none."""
        keys: list[str] = []
        for k in sort:
            for x, kind in self.sort_exprs(self.ref(a, self.c(k.col)), ks[k.col]):
                keys.append(self.d.sort_key(x, k.desc, k.nulls_first, kind))
        if keys and not self.tie_free:
            keys.append(self.asc(self.ordinal(a)))
        return keys

    def distinct(self, i: Rel, ordered: bool) -> str:
        """`dedup`: rows equal as `Value`s (NULLs equal, one zero and one NaN)
        are one; the first of them stays, in place."""
        d = self.d
        a = self.alias()
        ks = kinds(i)
        n = len(ks)
        keys = [self.ref(a, self.c(j)) for j in range(n)]
        if not ordered:
            # Any row of a group stands for it: they are all the same value.
            return self.select(
                self.passthrough(a, n, False),
                d.subquery(self.rel(i, False), a),
                "GROUP BY " + ", ".join(keys),
            )
        first = d.quote("first")
        over = d.over(keys, [self.asc(self.ordinal(a))])
        items = self.passthrough(a, n, True) + [f"{d.row_number(over)} AS {first}"]
        b = self.alias()
        return self.select(
            self.passthrough(b, n, True),
            d.subquery(self.select(items, d.subquery(self.rel(i, True), a)), b),
            f"WHERE {self.ref(b, first)} = {d.int_lit(1)}",
        )

    def window(self, i: Rel, part: tuple, sort: tuple, fns: tuple, ordered: bool) -> str:
        d = self.d
        a = self.alias()
        ks = kinds(i)
        m = len(ks)
        if (
            any(p >= m for p in part)
            or any(k.col >= m for k in sort)
            or any(f.reads and f.col >= m for f in fns)
        ):
            raise Unsupported("window refers to a column beyond its input")

        def col(j: int) -> str:
            return self.ref(a, self.c(j))

        partition = [col(p) for p in part]
        keys: list[str] = []
        for k in sort:
            for x, kind in self.sort_exprs(col(k.col), ks[k.col]):
                keys.append(d.sort_key(x, k.desc, k.nulls_first, kind))
        copies = numbers_copies(Window(i, part, sort, fns)) and not ordered
        if copies:
            # Any order numbers the copies (some dialects need one).
            keys = [d.sort_key(col(p), False, False, ks[p]) for p in part]
        elif not self.tie_free:
            # Lean sorts with a stable merge sort: ties keep their input order.
            keys.append(self.asc(self.ordinal(a)))
        elif ordered and not keys:
            raise Unsupported(
                "without ORDER BY a window keeps its input's order, which needs ordinals"
            )
        over = d.over(partition, keys)
        # Ranks, `CUME_DIST` and RANGE frames depend on the sort keys only: ties
        # are peers, not ordered by the ordinal.
        peers = keys[:-1] if not self.tie_free else keys

        def whole() -> str:
            return f"OVER ({'PARTITION BY ' + ', '.join(partition) if partition else ''})"

        items = [f"{col(j)} AS {self.c(j)}" for j in range(m)]
        for j, f in enumerate(fns):
            if f.fn == "row_number":
                sql = d.row_number(over)
            elif f.fn in ("lag", "lead"):
                default = self.lit(f.default, ks[f.col])
                fn = d.lag if f.fn == "lag" else d.lead
                sql = fn(col(f.col), f.offset, default, over)
            elif f.fn in ("rank", "dense_rank"):
                sql = f"{f.fn.upper()}() {d.over(partition, peers)}"
            elif f.fn == "ntile":
                # DataFusion's NTILE: ⌊i · min(k, n) / n⌋ + 1 for the i-th row
                # (from 0) of n.
                pos = f"({d.row_number(over)} - {d.int_lit(1)})"
                n = f"COUNT(*) {whole()}"
                k = f"LEAST({d.int_lit(f.offset)}, {n})"
                sql = f"({d.trunc_div(f'({pos} * {k})', n)} + {d.int_lit(1)})"
            elif f.fn in ("percent_rank", "cume_dist"):
                n = f"COUNT(*) {whole()}"
                if f.fn == "percent_rank":
                    r = f"(RANK() {d.over(partition, peers)} - {d.int_lit(1)})"
                    ratio = d.float_div(
                        d.int_to_float(r), d.int_to_float(f"({n} - {d.int_lit(1)})")
                    )
                    sql = d.case_when(f"{n} <= {d.int_lit(1)}", d.float_lit(0.0), ratio)
                else:
                    upto = f"COUNT(*) {d.over(partition, peers)}"
                    sql = d.float_div(d.int_to_float(upto), d.int_to_float(n))
            else:
                exact = f.measure is not None and f.measure.fn in ("count", "sum", "min", "max")
                if f.frame == WHOLE and f.fn == "agg" and exact:
                    # The whole partition, in any order.
                    w = whole()
                else:
                    w = self.framed(f.frame, partition, keys, peers, sort, ks)
                if f.fn == "agg":
                    assert f.measure is not None
                    sql = self.window_measure(f.measure, col, ks, w)
                elif f.fn == "nth_value":
                    sql = f"NTH_VALUE({col(f.col)}, {f.offset}) {w}"
                else:
                    sql = f"{f.fn.upper()}({col(f.col)}) {w}"
            items.append(f"{sql} AS {self.c(m + j)}")
        if ordered:
            # `windowEval` emits the rows in sort order.
            items.append(f"{d.row_number(self.order_by(keys))} AS {d.quote(ORD)}")
        return self.select(items, d.subquery(self.rel(i, not self.tie_free and not copies), a))

    def framed(
        self,
        fr: Frame,
        partition: list[str],
        keys: list[str],
        peers: list[str],
        sort: tuple,
        ks: list[Kind | None],
    ) -> str:
        """`OVER (…)` with the frame `fr`: ROWS frames order ties by the
        ordinal, as Lean's stable sort; RANGE frames by the keys alone."""
        d = self.d
        if not fr.range:
            order = keys
        elif any(b[0] != "unbounded" and b[1] != 0 for b in (fr.lo, fr.hi)):
            if self.tie_free is False and len(peers) != 1:
                raise Unsupported("RANGE frames with offsets need one sort key")
            order = peers
        else:
            order = peers

        def bound(b: tuple[str, int], lower: bool) -> str:
            side, k = b
            if side == "unbounded":
                return "UNBOUNDED PRECEDING" if lower else "UNBOUNDED FOLLOWING"
            if k == 0:
                return "CURRENT ROW"
            word = "PRECEDING" if side == "preceding" else "FOLLOWING"
            if fr.range:
                kind = ks[sort[0].col]
                if kind == "time":
                    return f"{d.interval_lit(k)} {word}"
                if kind == "date":
                    return f"{d.day_interval(k)} {word}"
            return f"{k} {word}"

        unit = "RANGE" if fr.range else "ROWS"
        spec = f"{unit} BETWEEN {bound(fr.lo, True)} AND {bound(fr.hi, False)}"
        return d.over_frame(partition, order, spec)

    def window_measure(
        self, m: Measure, col: Callable[[int], str], ks: list[Kind | None], w: str
    ) -> str:
        """`Measure.eval` over the frame `w` (the argument is a column or a
        constant, `Parse.issueFree`)."""
        d = self.d
        v = self.expr(m.arg, col, ks, None)
        match m.fn:
            case "count":
                return f"COUNT({v}) {w}"
            case "sum":
                return d.window_int_sum(v, w)
            case "fsum" | "avg":
                total = d.window_float_sum(v, w)
                if m.fn == "avg":
                    total = d.canon(d.float_div(total, d.int_to_float(f"COUNT({v}) {w}")))
                return d.case_when(f"COUNT({v}) {w} = {d.int_lit(0)}", d.null("float"), total)
        f = "MIN" if m.fn == "min" else "MAX"
        if expr_kind(m.arg, ks) == "bool":
            as_int = d.case_when(v, d.int_lit(1), d.int_lit(0))
            inner = d.case_when(f"{v} IS NULL", d.null("int"), as_int)
            return f"({f}({inner}) {w} = {d.int_lit(1)})"
        return f"{f}({v}) {w}"

    def sort_exprs(self, x: str, kind: Kind | None) -> list[tuple[str, Kind | None]]:
        """Expressions (and their kinds) that sort like `Value.le` on a column,
        NULL exactly when the value is NULL."""
        if kind != "float":
            return [(x, kind)]
        return [(self.d.float_rank(x), "int"), (x, "float")]

    def check_refs(self, e: Expr, n: int) -> None:
        match e:
            case Field(index=i):
                if i >= n:
                    raise Unsupported(
                        f"field reference ${i} is out of range (the input has {n} columns)"
                    )
            case Un(arg=a):
                self.check_refs(a, n)
            case Bin(left=a, right=b):
                self.check_refs(a, n)
                self.check_refs(b, n)
            case If(cond=c, then=t, orelse=o):
                for x in (c, t, o):
                    self.check_refs(x, n)

    # Expressions

    def lit(self, lit: Lit, ctx: Kind | None) -> str:
        d = self.d
        v, k = lit.value, lit.kind
        if v is None:
            return d.null(k or ctx)
        match k:
            case "bool":
                return d.bool_lit(v)
            case "str":
                return d.str_lit(v)
            case "float":
                return d.float_lit(v)
        if not I64_MIN <= v <= I64_MAX:
            raise Unsupported(f"integer constant {v} does not fit in 64 bits")
        match k:
            case "time":
                return d.timestamp_lit(v)
            case "date":
                return d.date_lit(v)
            case "tod":
                return d.time_of_day_lit(v)
            case "interval":
                return d.interval_lit(v)
        return d.int_lit(v)

    def expr(
        self, e: Expr, ref: Callable[[int], str], cols: list[Kind | None], ctx: Kind | None
    ) -> str:
        d = self.d

        def go(x: Expr, k: Kind | None = None) -> str:
            return self.expr(x, ref, cols, k)

        def kind(x: Expr) -> Kind | None:
            return expr_kind(x, cols)

        match e:
            case Lit():
                return self.lit(e, ctx)
            case Field(index=i):
                return ref(i)
            case Un(op="not", arg=a):
                return d.not3(go(a, "bool"))
            case Un(op="is_null", arg=a):
                return d.is_null(go(a))
            case Un(op="neg", arg=a):
                if kind(a) == "interval":
                    return d.interval_sub(d.interval_lit(0), go(a))
                return d.int_neg(self.int_operand(a, ref, cols, "negation"))
            case Un(op="itof", arg=a):
                return d.int_to_float(self.int_operand(a, ref, cols, "CAST to DOUBLE"))
            # IEEE makes `-0.0` here from the one zero (negation, rounding
            # up to zero, a negative times zero, underflow): `canon` it.
            case Un(op="fneg", arg=a):
                return d.canon(d.float_neg(self.float_operand(a, ref, cols)))
            case Un(op="ffloor" | "fceil" | "fround" as op, arg=a):
                f = {"ffloor": d.float_floor, "fceil": d.float_ceil, "fround": d.float_round}[op]
                return d.canon(f(self.float_operand(a, ref, cols)))
            case Un(op="froundTo", arg=a, digits=digits):
                return d.canon(d.float_round_to(self.float_operand(a, ref, cols), digits))
            case Un(op="ftoi", arg=a):
                return d.float_to_int(self.float_operand(a, ref, cols))
            case Un(op="narrow", arg=a, digits=bits):
                x = self.int_operand(a, ref, cols, "CAST to INT")
                lo, hi = d.int_lit(-(2 ** (bits - 1))), d.int_lit(2 ** (bits - 1) - 1)
                fail = d.raise_(f"CAST to a {bits}-bit integer out of range", x, "int")
                return f"(CASE WHEN {x} BETWEEN {lo} AND {hi} THEN {x} ELSE {fail} END)"
            case Un(op="itos", arg=a):
                return d.int_to_str(self.int_operand(a, ref, cols, "CAST to VARCHAR"))
            case Bin(op="and" | "or" as op, left=a, right=b):
                f = d.and3 if op == "and" else d.or3
                return f(go(a, "bool"), go(b, "bool"))
            case Un(op="fmath", arg=a, param=name):
                x = self.float_operand(a, ref, cols)
                return self.domain(x, self.domain_error(name, x), d.canon(d.float_fn(name, x)))
            case Bin(op="fatan2", left=a, right=b):
                y, x = self.float_operand(a, ref, cols), self.float_operand(b, ref, cols)
                zero = d.float_lit(0.0)
                bad = f"({d.float_eq(y, zero)} AND {d.float_eq(x, zero)})"
                return self.domain(y, bad, d.canon(d.float_atan2(y, x)))
            case Bin(op="flogb", left=a, right=b):
                x, base = self.float_operand(a, ref, cols), self.float_operand(b, ref, cols)
                zero = d.float_lit(0.0)
                bad = (
                    f"(NOT {d.float_lt(zero, x)} OR NOT {d.float_lt(zero, base)} "
                    f"OR {d.float_eq(base, d.float_lit(1.0))})"
                )
                return self.domain(x, bad, d.canon(d.float_logb(x, base)))
            case Bin(op="bit", left=a, right=b, param=name):
                sa, sb = (self.int_operand(e, ref, cols, name) for e in (a, b))
                sql = d.bitwise(name, sa, sb)
                if "shift" not in name:
                    return sql
                bad = f"({sb} < {d.int_lit(0)} OR {sb} > {d.int_lit(63)})"
                return self.domain(sb, bad, sql, "int")
            case Bin(op="fadd" | "fsub" | "fmul" | "fdiv" | "fpow" as op, left=a, right=b):
                f = {
                    "fadd": d.float_add,
                    "fsub": d.float_sub,
                    "fmul": d.float_mul,
                    "fdiv": d.float_div,
                    "fpow": d.float_pow,
                }[op]
                sql = f(self.float_operand(a, ref, cols), self.float_operand(b, ref, cols))
                # A sum or difference of doubles other than -0.0 is never -0.0.
                return sql if op in ("fadd", "fsub") else d.canon(sql)
            case Bin(op="add" | "sub" | "mul" as op, left=a, right=b):
                return self.arith(op, a, b, ref, cols)
            case Bin(op="idiv" | "imod" as op, left=a, right=b):
                what = "division" if op == "idiv" else "remainder"
                sa = self.int_operand(a, ref, cols, what)
                sb = self.int_operand(b, ref, cols, what)
                return d.int_div(sa, sb) if op == "idiv" else d.int_mod(sa, sb)
            case Bin(op="ipow", left=a, right=b):
                if isinstance(b, Lit) and b.value is None:
                    return d.null("int")
                sa = self.int_operand(a, ref, cols, "POWER")
                if isinstance(b, Lit) and isinstance(b.value, int) and b.kind == "int":
                    return d.int_pow(sa, b.value)
                return d.int_pow_var(sa, self.int_operand(b, ref, cols, "POWER"))
            case Bin(op="eq" | "lt" as op, left=a, right=b):
                ka, kb = kind(a), kind(b)
                k = ka or kb
                if ka is not None and kb is not None and ka != kb:
                    raise Unsupported(f"comparison of {ka} with {kb}; cast one side first")
                if op == "lt" and k in ("str", "bool"):
                    # `BinFn.apply .lt` is only defined on integers (and the codes).
                    raise Unsupported(
                        f"ordering comparisons of {k} values are not in the Lean model"
                    )
                sa, sb = go(a, k), go(b, k)
                if k == "float":
                    return d.float_eq(sa, sb) if op == "eq" else d.float_lt(sa, sb)
                return d.eq(sa, sb) if op == "eq" else d.lt(sa, sb)
            case If(cond=c, then=t, orelse=o):
                k = kind(e) or ctx
                return d.case_when(go(c, "bool"), go(t, k), go(o, k))
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
            case Un(op="date_part", arg=a, param=part) if kind(a) == "tod":
                return d.time_part(part, self.operand(a, "tod", ref, cols, "date_part"))
            case Un(op="date_part", arg=a, param=part):
                return d.date_part(part, self.operand(a, "time", ref, cols, "date_part"))
            case Un(op="time_of_day", arg=a):
                x = self.operand(a, "time", ref, cols, "CAST to TIME")
                return self.chrono_only(x, d.time_of_day(x), "CAST to TIME", "tod")
            case Un(op="bucket", arg=a, digits=k, origin=origin):
                # `Time.bucket`, in integer microseconds; DataFusion's nanoseconds
                # wrap outside ±2⁶³, where it is an error here.
                x = self.operand(a, "time", ref, cols, "date_bin")
                us = d.time_micros(x)
                rel = f"({us} - {d.int_lit(origin)})"
                k_ = d.int_lit(k)
                floor = f"(({d.trunc_mod(rel, k_)} + {k_}) % {k_})"
                r = d.as_time(f"({us} - {floor})")
                if not d.guards:
                    return r
                lo, hi = d.int_lit(NS_MIN), d.int_lit(NS_MAX)
                fail = d.raise_("date_bin outside ±2^63 ns", x, "time")
                ru = d.time_micros(r)
                bad = f"({us} NOT BETWEEN {lo} AND {hi} OR {ru} NOT BETWEEN {lo} AND {hi})"
                return d.case_when(bad, fail, r)
            case Un(op="as_time", arg=a):
                return d.as_time(self.int_operand(a, ref, cols, "CAST to TIMESTAMP"))
            case Un(op="strftime", arg=a, param=fmt):
                x = self.operand(a, "time", ref, cols, "strftime")
                return self.chrono_only(x, self.strftime(x, fmt), "strftime", "str")
            case Un(op="date_trunc", arg=a, param=unit):
                return self.date_trunc(unit, self.operand(a, "time", ref, cols, "date_trunc"))
            case Un(op="to_date", arg=a):
                return d.to_date(self.operand(a, "time", ref, cols, "CAST to DATE"))
            case Un(op="day_part", arg=a, param=part):
                x = self.operand(a, "date", ref, cols, "date_part")
                inside = f"{d.date_days(x)} BETWEEN {d.int_lit(DAY_MIN)} AND {d.int_lit(DAY_MAX)}"
                return f"(CASE WHEN {inside} THEN {d.date_part(part, d.date_to_time(x))} END)"
            case Un(op="day_trunc", arg=a, param=unit):
                x = self.operand(a, "date", ref, cols, "date_trunc")
                return self.date_range(
                    x,
                    lambda y: d.to_date(d.date_trunc(unit, d.date_to_time(y))),
                    NS_DAY_MIN,
                    NS_DAY_MAX,
                    f"date_trunc to a {unit}",
                )
            case Un(op="add_months", arg=a, digits=months, param=k):
                kind: Kind = "time" if k == "time" else "date"
                x = self.operand(a, kind, ref, cols, "adding months")
                if kind == "date":
                    return self.date_range(
                        x, lambda y: d.add_months(y, months, kind), DAY_MIN, DAY_MAX,
                        "adding months",
                    )  # fmt: skip
                if not d.guards:
                    return d.add_months(x, months, kind)
                lo, hi = d.int_lit(PART_MIN), d.int_lit(PART_MAX)
                us = d.time_micros(x)
                fail = d.raise_("adding months outside the years chrono represents", x, "time")
                safe = d.add_months(
                    f"(CASE WHEN {us} BETWEEN {lo} AND {hi} THEN {x} END)", months, kind
                )
                return d.case_when(
                    f"({us} NOT BETWEEN {lo} AND {hi} "
                    f"OR {d.time_micros(safe)} NOT BETWEEN {lo} AND {hi})",
                    fail,
                    safe,
                )
            case Bin(op="date_add", left=a, right=b):
                x = self.operand(a, "date", ref, cols, "date + days")
                n = self.int_operand(b, ref, cols, "date + days")
                return self.date_range(
                    x, lambda y: d.date_add_days(y, n), DAY_MIN, DAY_MAX, "date + days"
                )
            case Bin(op="date_diff", left=a, right=b):
                x = self.operand(a, "date", ref, cols, "date_diff")
                y = self.operand(b, "date", ref, cols, "date_diff")
                return d.date_diff_days(x, y)
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
                return self.ascii_only(
                    d.concat(sa, sb), d.levenshtein(sa, sb), "levenshtein", "int"
                )
            case Bin(op="substr", left=a, right=b, length=length):
                sa = self.operand(a, "str", ref, cols, "substring")
                sb = self.int_operand(b, ref, cols, "substring")
                return self.substring(sa, sb, length)
            case Bin(op="trim", left=a, right=b, sides=sides):
                sa, sb = (self.operand(x, "str", ref, cols, "trim") for x in (a, b))
                return d.trim(sa, sb, *sides)
        raise Unsupported(f"unsupported expression {e!r}")

    def operand(
        self, e: Expr, want: Kind, ref: Callable[[int], str], cols: list[Kind | None], what: str
    ) -> str:
        """`e` as a value of kind `want` (an untyped NULL is one too)."""
        k = expr_kind(e, cols)
        if k != want and not (isinstance(e, Lit) and e.value is None):
            raise Unsupported(f"{what} needs a {want} value, not {k or 'one of unknown type'}")
        return self.expr(e, ref, cols, want)

    def substring(self, s: str, a: str, n: int | None) -> str:
        """`Text.substr`: the characters at 1-based positions `a … a+n-1` that
        exist. Engines count a start below 1 differently (from the end, or
        not at all), so only starts ≥ 1 reach them."""
        d = self.d
        one = d.int_lit(1)
        null = d.null("str")
        if n == 0:
            return d.case_when(f"({s} IS NULL OR {a} IS NULL)", null, d.str_lit(""))
        if n is None:
            return (
                f"(CASE WHEN {a} IS NULL THEN {null} WHEN {a} >= {one} "
                f"THEN {d.substring(s, a, None)} ELSE {s} END)"
            )
        # No string has 2^62 characters; `a + (n - 1)` cannot overflow for `a < 1`.
        m = min(n, 2**62)
        rest = f"GREATEST({a} + {d.int_lit(m - 1)}, {d.int_lit(0)})"
        return (
            f"(CASE WHEN {a} IS NULL THEN {null} WHEN {a} >= {one} "
            f"THEN {d.substring(s, a, d.int_lit(m))} ELSE {d.substring(s, one, rest)} END)"
        )

    def date_trunc(self, unit: str, ts: str) -> str:
        """`Time.trunc`. To a week or longer, DataFusion computes in nanoseconds
        and fails outside ±2⁶³ ns (`Issue.overflow`): so does the SQL. To a day
        or less it wraps below -2⁶³ µs, which no engine's timestamps reach."""
        d = self.d
        t = d.date_trunc(unit, ts)
        if unit not in ("week", "month", "quarter", "year") or not d.guards:
            return t
        lo, hi = d.timestamp_lit(NS_MIN), d.timestamp_lit(NS_MAX)
        fail = d.raise_(f"date_trunc to a {unit} outside ±2^63 ns", ts, "time")
        return d.case_when(f"({ts} > {hi} OR {t} < {lo})", fail, t)

    def chrono_only(self, ts: str, r: str, what: str, kind: Kind) -> str:
        """`r`, raising where the timestamp `ts` is outside the years chrono
        represents (DataFusion fails there)."""
        d = self.d
        if not d.guards:
            return r
        lo, hi = d.int_lit(PART_MIN), d.int_lit(PART_MAX)
        fail = d.raise_(f"{what} outside the years chrono represents", ts, kind)
        return d.case_when(f"({d.time_micros(ts)} NOT BETWEEN {lo} AND {hi})", fail, r)

    def strftime(self, ts: str, fmt: str) -> str:
        """`Time.strftime`, from `date_part`s: `%Y` padded to four digits,
        with a sign outside 0 to 9999, as chrono writes it."""
        d = self.d

        def part(p: str, width: int) -> str:
            return d.zero_pad(d.date_part(p, ts), width)

        y = d.date_part("year", ts)
        year = (
            f"(CASE WHEN {y} BETWEEN 0 AND 9999 THEN {d.zero_pad(y, 4)} "
            f"WHEN {y} > 9999 THEN {d.concat(d.str_lit('+'), d.int_to_str(y))} "
            f"ELSE {d.concat(d.str_lit('-'), d.zero_pad(f'(- {y})', 4))} END)"
        )
        pieces = {
            "%Y": year, "%m": part("month", 2), "%d": part("day", 2), "%H": part("hour", 2),
            "%M": part("minute", 2), "%S": part("second", 2), "%j": part("doy", 3),
        }  # fmt: skip
        pieces["%F"] = f"{year} || '-' || {pieces['%m']} || '-' || {pieces['%d']}"
        pieces["%T"] = f"{pieces['%H']} || ':' || {pieces['%M']} || ':' || {pieces['%S']}"
        tokens = parse_format(fmt) or []
        out = [pieces.get(t, d.str_lit("%" if t == "%%" else t)) for t in tokens]
        return "(" + " || ".join(out or [d.str_lit("")]) + ")"

    def date_range(self, x: str, f: Callable[[str], str], lo: int, hi: int, what: str) -> str:
        """`rangeIssue`: the DATE `f(x)`, raising unless `x` and it are within
        `[lo, hi]` days (DataFusion fails, or gives garbage). `f` sees only
        dates in range, so the engine's own range errors cannot come first."""
        d = self.d
        if not d.guards:
            return f(x)
        lo_, hi_ = d.int_lit(lo), d.int_lit(hi)
        r = f(f"(CASE WHEN {d.date_days(x)} BETWEEN {lo_} AND {hi_} THEN {x} END)")
        fail = d.raise_(f"{what} outside the dates DataFusion computes", x, "date")
        # NULL (so not raising) where `x` or the result is NULL.
        bad = (
            f"({d.date_days(x)} NOT BETWEEN {lo_} AND {hi_} "
            f"OR {d.date_days(r)} NOT BETWEEN {lo_} AND {hi_})"
        )
        return d.case_when(bad, fail, r)

    def ascii_only(self, x: str, value: str, what: str, kind: Kind = "str") -> str:
        """`value`, a black box of the string `x` that the engine computes as
        Rust does on ASCII text only, or an error where `x` is not ASCII
        (#70). Not one of `Safety.lean`'s issues, so `guards=False` keeps it."""
        d = self.d
        fail = d.raise_(f"{what} of non-ASCII text differs between engines", x, kind)
        return d.case_when(f"(NOT {d.is_ascii(x)})", fail, value)

    def int_operand(
        self, e: Expr, ref: Callable[[int], str], cols: list[Kind | None], what: str
    ) -> str:
        k = expr_kind(e, cols)
        if k not in ("int", None) or (k is None and not (isinstance(e, Lit) and e.value is None)):
            raise Unsupported(f"{what} needs an integer, not {k or 'a value of unknown type'}")
        sql = self.expr(e, ref, cols, "int")
        # Columns may be narrower than 64 bits; widen them so overflow means 64 bits.
        return sql if isinstance(e, Lit) or _is_int_arith(e) else self.d.cast(sql, "int")

    def domain_error(self, name: str, x: str) -> str:
        """Is the double `x` outside the domain of `FMath` `name`
        (`FMath.inDomain`)? NULL for NULL; NaN is in every domain."""
        d = self.d
        zero = d.float_lit(0.0)
        if name == "sqrt":
            return d.float_lt(x, zero)
        if name in ("ln", "log10", "log2"):
            return f"(NOT {d.float_lt(zero, x)})"
        if name in ("asin", "acos"):
            below, above = d.float_lt(x, d.float_lit(-1.0)), d.float_lt(d.float_lit(1.0), x)
            return f"({below} OR ({above} AND NOT {d.is_nan(x)}))"
        return d.bool_lit(False)

    def domain(self, dep: str, bad: str, sql: str, kind: Kind = "float") -> str:
        """`sql`, raising where the arguments are outside the function's
        domain (`Issue.domain`): Substrait's `on_domain_error` = ERROR."""
        if not self.d.guards or bad == self.d.bool_lit(False):
            return sql
        return self.d.case_when(bad, self.d.raise_("domain error", dep, kind), sql)

    def float_operand(self, e: Expr, ref: Callable[[int], str], cols: list[Kind | None]) -> str:
        k = expr_kind(e, cols)
        if k != "float" and not (isinstance(e, Lit) and e.value is None):
            # Lean would read the integer as a double's code.
            raise Unsupported(
                f"double arithmetic on {k or 'a value of unknown type'}; cast it to DOUBLE first"
            )
        return self.expr(e, ref, cols, "float")

    def arith(
        self, op: str, a: Expr, b: Expr, ref: Callable[[int], str], cols: list[Kind | None]
    ) -> str:
        d = self.d
        ka, kb = expr_kind(a, cols), expr_kind(b, cols)
        sym = {"add": "+", "sub": "-", "mul": "*"}[op]
        if "float" in (ka, kb):
            raise Unsupported(
                f"integer {sym} on a double (Lean reads it as a code): needs an fp64 outputType"
            )
        temporal = {ka, kb} & {"time", "date", "interval"}
        if not temporal:
            name = {"add": "addition", "sub": "subtraction", "mul": "multiplication"}[op]
            sa, sb = self.int_operand(a, ref, cols, name), self.int_operand(b, ref, cols, name)
            return {"add": d.int_add, "sub": d.int_sub, "mul": d.int_mul}[op](sa, sb)
        if "date" in temporal:
            raise Unsupported(
                "date arithmetic is not in the Lean model (dates are days, intervals microseconds)"
            )
        sa, sb = self.expr(a, ref, cols, ka or kb), self.expr(b, ref, cols, kb or ka)
        match op, ka or kb, kb or ka:
            case "add", "time", "interval":
                return d.time_add_interval(sa, sb)
            case "add", "interval", "time":
                return d.time_add_interval(sb, sa)
            case "sub", "time", "interval":
                return d.time_sub_interval(sa, sb)
            case "sub", "time", "time":
                return d.time_diff(sa, sb)
            case "add", "interval", "interval":
                return d.interval_add(sa, sb)
            case "sub", "interval", "interval":
                return d.interval_sub(sa, sb)
        raise Unsupported(f"{ka} {sym} {kb} is not supported")


#: DataFusion truncates to calendar units exactly from here to here
#: (`Time.nsMin`, `Time.nsMax`, in microseconds).
NS_MIN, NS_MAX = -9223372036854775, 9223372036854775
#: The days chrono represents (`Time.dayMin`, `Time.dayMax`), the timestamps
#: (`Time.partMin`, `Time.partMax`), and the days within ±2⁶³ ns
#: (`Time.nsDayMin`, `Time.nsDayMax`).
DAY_MIN, DAY_MAX = -96465292, 95026236
PART_MIN, PART_MAX = -8334601228800000000, 8210266876799999999
NS_DAY_MIN, NS_DAY_MAX = -106751, 106751
#: The longest string DataFusion's `repeat` writes, in bytes (`Text.repeatMax`).
REPEAT_MAX = 2**31 - 1


def like_pattern(p: str) -> str:
    """`Text.tokens` as a pattern for `LIKE … ESCAPE '\\'`: a backslash escapes
    the next character, and a trailing one stands for itself (where SQL
    engines reject it), so it is escaped."""
    return p + "\\" if (len(p) - len(p.rstrip("\\"))) % 2 else p


def unicode_classes(p: str) -> bool:
    """Does the pattern use `\\d`, `\\w` or `\\s` (or their negations)? Rust's
    are Unicode classes; RE2's (DuckDB), Java's (Spark) and Snowflake's are
    ASCII-only, so they agree on ASCII text only."""
    i = 0
    while i < len(p):
        if p[i] == "\\" and i + 1 < len(p):
            if p[i + 1] in "dDwWsS":
                return True
            i += 2
        else:
            i += 1
    return False


def regex_groups(p: str) -> int:
    """The entries `regexp_match(s, p)` has on a match: its capture groups, or
    the whole match if there are none. Groups are counted as `(` outside
    classes and escapes, which is exact for patterns without `(?`."""
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
            if p[k + 1 : k + 2] == "?":
                raise Unsupported(f"regular expressions with '(?' are not supported: {p!r}")
            groups += 1
        k += 1
    return max(groups, 1)


def _is_int_arith(e: Expr) -> bool:
    """Is `e` computed as a BIGINT already?"""
    if isinstance(e, Bin):
        return e.op in ("add", "sub", "mul", "idiv", "imod", "ipow")
    return isinstance(e, Un) and e.op in ("neg", "ftoi")


def _no_fields() -> str:
    raise Unsupported("virtual table rows cannot refer to fields")


def to_sql(plan: dict, dialect: Dialect, *, tie_free: bool = False, guards: bool = True) -> str:
    """SQL for a Substrait JSON plan, with the semantics `Rel.eval` gives it.

    The result has the plan's output names (`RelRoot.names`, else `c0`, …),
    and is ordered as Lean orders it when the plan has a FETCH or a window.
    Raises `Unsupported` for plans outside the Lean model. This is
    `sverify.engines.to_sql`.

    `tie_free=True` promises that no two rows tie on any window's PARTITION BY
    and ORDER BY columns (what a contract report's `deterministic` says). Then
    windows need no ordinal tiebreak, so engines without a stable scan order
    can run them; FETCH still needs one.

    `guards=False` leaves out the run-time checks (`Dialect.guards`). Only
    pass it for a plan whose contract report is `guard_free`, and run the
    SQL on data that meets the contract's preconditions.

    Args:
        plan: A Substrait JSON plan, parsed (`json.loads`), such as a
            node's `plan` or `sverify.engines.written_plan`'s output.
        dialect: The engine to write SQL for: `sverify.engines.DUCKDB`,
            `sverify.engines.SNOWFLAKE` or `sverify.engines.SPARK`.
        tie_free: Promise that windows have no ties on their PARTITION BY
            and ORDER BY columns. Default: False.
        guards: Write the run-time checks. Default: True.

    Returns:
        One SQL query in the dialect. It reads the plan's tables by their
        names, quoted.

    Raises:
        Unsupported: The plan is outside the Lean model, its root names do
            not match its columns, or the dialect cannot express it.

    Examples:
        The plan of a transform, as Snowflake SQL:

        ```python
        import json

        import pyarrow as pa
        import sverify as sv
        from sverify.engines import SNOWFLAKE, to_sql
        from sverify.io import StaticSource

        orders = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders")


        @sv.transform()
        def big_orders(orders):
            return orders.filter(orders.amount > 10)


        print(to_sql(json.loads(big_orders(orders).plan), SNOWFLAKE))
        # SELECT s1."c0" AS "id", s1."c1" AS "amount" FROM (SELECT s2."c0" AS "c0", ...
        ```
    """
    if not guards:
        dialect = replace(dialect, guards=False)
    p = parse_plan(plan)
    n = arity(p.root)
    names = p.names or [f"c{i}" for i in range(n)]
    if len(names) != n:
        raise Unsupported(f"root names {names} do not match the plan's {n} columns")
    for k in kinds(p.root):
        dialect.result_kind(k)
    w = _Writer(dialect, tie_free)
    ordered = order_matters(p.root)
    a = w.alias()
    items = [f"{w.ref(a, w.c(i))} AS {dialect.quote(name)}" for i, name in enumerate(names)]
    rest = f"ORDER BY {w.asc(w.ordinal(a))}" if ordered else ""
    return w.select(items, dialect.subquery(w.rel(p.root, ordered), a), rest)

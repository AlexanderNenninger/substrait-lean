"""Snowflake SQL with the Lean model's semantics.

Every hook either emits SQL whose result Snowflake's documentation pins down
to the Lean value, or raises `Unsupported`; where only the data can tell
(an i64 overflow, two float zeros compared), the SQL raises at run time
instead of returning a different answer. The divergences, with the
documentation they rest on:

* **Integers** are `NUMBER(38,0)` (`BIGINT` is an alias). Arithmetic on two
  i64 values is exact (|a·b| < 2¹²⁶ < 10³⁸), so each result is checked
  against the i64 range and an overflow raises, as on the other engines.
* **Integer division**: `/` returns a decimal rounded to 6 places, not a
  truncated integer, so truncating it can be off by one. `MOD` has the sign
  of the dividend (truncating, as `Int.tmod`), and `a - MOD(a, b)` divides
  exactly. `CAST(x AS NUMBER)` of a float rounds, so it is `TRUNC(x)` cast,
  after NaN, ±inf and values outside 64 bits raise.
* **NULL order** defaults to the session's `DEFAULT_NULL_ORDERING`; the sort
  keys always say `NULLS FIRST`/`NULLS LAST`.
* **Three-valued logic**: `AND`/`OR`/`NOT` are Kleene, as in Lean. There is
  no `IS TRUE`, so it is `COALESCE(x, FALSE)`.
* **Floats** are IEEE doubles; all NaNs are equal and NaN is above `'inf'`
  (documented), as in the model, which has one NaN and one zero. `canon`
  turns a `-0.0` into `0.0` wherever one could arise, so whether Snowflake
  shows the sign of a zero does not matter.
* **Timestamps** are `TIMESTAMP_NTZ(6)`: wall-clock microseconds like Lean.
  Plain `TIMESTAMP` follows `TIMESTAMP_TYPE_MAPPING` and defaults to
  nanoseconds; `LTZ` would depend on the session time zone. There is no
  interval type, only interval constants added to a timestamp, so
  interval-valued expressions are refused.
* **Strings**: a backslash is an escape character in a quoted literal, so
  it is doubled. Without a collation, strings compare by UTF-8 bytes, which
  is Lean's code point order; `LENGTH`, `POSITION` and `SUBSTR` count
  characters. `POSITION('' IN s)` is not documented, so an empty needle is 1
  by a `CASE`. Regular expressions are POSIX extended with Perl's `\\d`,
  `\\w` and `\\s` (black boxes in Lean); `REGEXP_INSTR` searches, where
  `REGEXP_LIKE` would match the whole string.
* **Dates**: `DAYOFWEEK`, `WEEK` and `DATE_TRUNC('WEEK')` depend on the
  session's `WEEK_START` and `WEEK_OF_YEAR_POLICY`, so the SQL uses the ISO
  forms (`DAYOFWEEKISO`, `WEEKISO`) and truncates to Monday itself. There is
  no sub-minute millisecond part: it is `SECOND` and `NANOSECOND` combined.
  `TIMESTAMP_NTZ` stays within the years chrono represents, so `date_part`
  is never NULL for a non-NULL timestamp, as in Lean.
* **Windows**: `LAG`/`LEAD` take the default when the offset leaves the
  partition, as in Lean; `ORDER BY` is required. Tables have no row order
  (no `rowid`), so nothing can stand for Lean's list order, which FETCH and
  ties in a window follow: `row_ordinal` is refused. Windows run with
  `to_sql(..., tie_free=True)`, when the caller knows there are no ties.
* **Identifiers** fold to upper case unless quoted; every one is quoted.
"""

from __future__ import annotations

import datetime as dt
import math
from collections.abc import Sequence
from dataclasses import dataclass

from sverify.sql.core import Dialect, Kind, Unsupported

I64_MIN, I64_MAX = -(2**63), 2**63 - 1
NAN = "CAST('NaN' AS FLOAT)"
EPOCH = dt.datetime(1970, 1, 1)

_TYPES: dict[str, str] = {
    "int": "NUMBER(38,0)",
    "float": "FLOAT",
    "time": "TIMESTAMP_NTZ(6)",
    "date": "DATE",
    "str": "VARCHAR",
    "bool": "BOOLEAN",
}


@dataclass(frozen=True)
class SnowflakeDialect(Dialect):
    def type_name(self, kind: Kind) -> str:
        if kind not in _TYPES:
            raise Unsupported(f"Snowflake has no {kind} type (intervals are only constants)")
        return _TYPES[kind]

    def raise_(self, message: str, dep: str, kind: Kind) -> str:
        """An expression of type `kind` that fails with `message`. Snowflake
        has no RAISE function, but casting a non-numeric (non-boolean) string
        is an error that quotes the string. It depends on `dep` so it cannot
        be folded at compile time, and is NULL when `dep` is."""
        msg = self.str_lit(f"sverify: {message}: ")
        return f"CAST({msg} || TO_VARCHAR({dep}) AS {self.type_name(kind)})"

    # Literals

    def str_lit(self, s: str) -> str:
        # Control characters as escapes, so every query is one line of text.
        s = s.replace("\\", "\\\\").replace("'", "''")
        for c, e in (("\n", "\\n"), ("\r", "\\r"), ("\t", "\\t"), ("\0", "\\0")):
            s = s.replace(c, e)
        return "'" + "".join(f"\\u{ord(c):04x}" if ord(c) < 32 else c for c in s) + "'"

    def float_lit(self, f: float) -> str:
        if math.isnan(f):
            return NAN
        if math.isinf(f):
            return "CAST('inf' AS FLOAT)" if f > 0 else "CAST('-inf' AS FLOAT)"
        return f"CAST('{f + 0.0!r}' AS FLOAT)"  # `+ 0.0`: the one zero

    def int_lit(self, i: int) -> str:
        return str(i)

    def timestamp_lit(self, micros: int) -> str:
        try:
            t = EPOCH + dt.timedelta(microseconds=micros)
        except OverflowError as e:
            raise Unsupported(f"timestamp {micros} µs is outside years 1-9999") from e
        return f"CAST('{t:%Y-%m-%d %H:%M:%S.%f}' AS TIMESTAMP_NTZ(6))"

    def date_lit(self, days: int) -> str:
        try:
            d = EPOCH.date() + dt.timedelta(days=days)
        except OverflowError as e:
            raise Unsupported(f"date {days} days is outside years 1-9999") from e
        return f"CAST('{d:%Y-%m-%d}' AS DATE)"

    def interval_lit(self, micros: int) -> str:
        # One constant in microseconds: exact, and the documentation's own
        # examples use counts above 2³² ('5000000001 nanoseconds'). Constants
        # take no sign inside, so a negative one is `- INTERVAL …`, which only
        # the two timestamp hooks below consume.
        sign = "- " if micros < 0 else ""
        return f"{sign}INTERVAL '{abs(micros)} microseconds'"

    # Integers: exact NUMBER(38,0) arithmetic, then the i64 range check.

    def checked(self, r: str, *, row: bool = True) -> str:
        """`r` if it fits in 64 bits, else an error. Row-level checks go
        with `guards=False`; the one on `SUM` (`row=False`) stays."""
        if row and not self.guards:
            return r
        fail = self.raise_("integer overflow", r, "int")
        return f"IFF({r} BETWEEN {I64_MIN} AND {I64_MAX}, {r}, {fail})"

    def int_add(self, a: str, b: str) -> str:
        return self.checked(f"({a} + {b})")

    def int_sub(self, a: str, b: str) -> str:
        return self.checked(f"({a} - {b})")

    def int_mul(self, a: str, b: str) -> str:
        return self.checked(f"({a} * {b})")

    def int_neg(self, a: str) -> str:
        return self.checked(f"(- {a})")

    def trunc_div(self, a: str, b: str) -> str:
        # Exact: `a - MOD(a, b)` is a multiple of `b`. Only MIN / -1 leaves 64 bits.
        return self.checked(f"CAST(({a} - MOD({a}, {b})) / {b} AS NUMBER(38,0))")

    def trunc_mod(self, a: str, b: str) -> str:
        return f"MOD({a}, {b})"

    # Doubles

    def float_to_int(self, x: str) -> str:
        # Doubles in [-2^63, 2^63) truncate into 64 bits; the float NaN is
        # above 'inf', so the range check rejects it too.
        lo, hi = self.float_lit(-(2.0**63)), self.float_lit(2.0**63)
        value = f"CAST(TRUNC({x}) AS NUMBER(38,0))"
        if not self.guards:
            return value
        fail = self.raise_("CAST to BIGINT out of range", x, "int")
        return f"(CASE WHEN {x} >= {lo} AND {x} < {hi} THEN {value} ELSE {fail} END)"

    def int_to_float(self, a: str) -> str:
        return f"CAST({a} AS FLOAT)"

    def float_fn(self, name: str, x: str) -> str:
        raise Unsupported(
            f"Snowflake's {name.upper()} is not documented to be C's libm, which the Lean model uses"
        )

    def float_atan2(self, y: str, x: str) -> str:
        raise Unsupported("Snowflake's ATAN2 is not documented to be C's libm")

    def bitwise(self, op: str, a: str, b: str) -> str:
        # Exact on 64-bit integers; shifts beyond the width are not documented.
        fn = {"bitwise_and": "BITAND", "bitwise_or": "BITOR", "bitwise_xor": "BITXOR"}.get(op)
        if fn is None:
            raise Unsupported(f"Snowflake's shifts by 64 or more bits are not documented ({op})")
        return f"{fn}({a}, {b})"

    def is_nan(self, x: str) -> str:
        return f"({x} = {NAN})"

    def float_eq(self, a: str, b: str) -> str:
        return f"({a} = {b})"

    def float_lt(self, a: str, b: str) -> str:
        return f"({a} < {b})"

    # Temporal

    def time_add_interval(self, ts: str, iv: str) -> str:
        if iv.startswith("- "):
            return f"({ts} - {iv[2:]})"
        return f"({ts} + {iv})"

    def time_sub_interval(self, ts: str, iv: str) -> str:
        if iv.startswith("- "):
            return f"({ts} + {iv[2:]})"
        return f"({ts} - {iv})"

    def time_diff(self, a: str, b: str) -> str:
        raise Unsupported("Snowflake has no interval values, so timestamp - timestamp is refused")

    def interval_add(self, a: str, b: str) -> str:
        raise Unsupported("Snowflake has no interval values to add")

    def interval_sub(self, a: str, b: str) -> str:
        raise Unsupported("Snowflake has no interval values to subtract")

    def date_part(self, part: str, ts: str) -> str:
        fn = {"week": "WEEKISO", "doy": "DAYOFYEAR"}.get(part, part.upper())
        sec, ns = f"SECOND({ts})", f"EXTRACT(NANOSECOND FROM {ts})"
        if part == "millisecond":
            return f"({sec} * 1000 + FLOOR({ns} / 1000000))"
        if part == "microsecond":
            return f"({sec} * 1000000 + FLOOR({ns} / 1000))"
        if part == "dow":
            return f"MOD(DAYOFWEEKISO({ts}), 7)"
        return f"{fn}({ts})"

    def date_trunc(self, unit: str, ts: str) -> str:
        if unit == "microsecond":
            return ts
        if unit == "week":
            day = f"DATE_TRUNC('DAY', {ts})"
            return f"DATEADD(DAY, 1 - DAYOFWEEKISO({ts}), {day})"
        return f"DATE_TRUNC('{unit.upper()}', {ts})"

    # Aggregates

    def int_sum(self, v: str) -> str:
        # NUMBER(38,0) sums are exact far beyond 64 bits.
        return f"CAST({self.checked(f'SUM({v})', row=False)} AS NUMBER(38,0))"

    def float_sum(self, v: str, o: str) -> str:
        raise Unsupported(
            "Snowflake does not add doubles in a given order, and the rounding of a SUM or "
            "AVG of doubles depends on it"
        )

    # Strings

    def char_length(self, s: str) -> str:
        return f"LENGTH({s})"

    def strpos(self, s: str, t: str) -> str:
        return (
            f"(CASE WHEN {s} IS NULL OR {t} IS NULL THEN NULL WHEN {t} = {self.str_lit('')} "
            f"THEN 1 ELSE POSITION({t} IN {s}) END)"
        )

    def starts_with(self, s: str, t: str) -> str:
        return f"STARTSWITH({s}, {t})"

    def ends_with(self, s: str, t: str) -> str:
        return f"ENDSWITH({s}, {t})"

    def like_pattern(self, p: str) -> str:
        # Ends with an odd number of backslashes: a non-backslash (or nothing),
        # then pairs, then one (REGEXP_LIKE matches the whole string).
        odd = f"REGEXP_LIKE({p}, {self.str_lit(r'(.*[^\\])?(\\\\)*\\')}, 's')"
        return f"IFF({odd}, {p} || {self.str_lit(chr(92))}, {p})"

    def substring(self, s: str, start: str, length: str | None) -> str:
        return f"SUBSTR({s}, {start})" if length is None else f"SUBSTR({s}, {start}, {length})"

    def trim(self, s: str, chars: str, left: bool, right: bool) -> str:
        f = "TRIM" if left and right else "LTRIM" if left else "RTRIM"
        return f"{f}({s}, {chars})"

    def regex_search(self, s: str, pattern: str) -> str:
        return f"(REGEXP_INSTR({s}, {self.str_lit(pattern)}) > 0)"

    # Logic

    def is_true(self, a: str) -> str:
        return f"COALESCE({a}, FALSE)"

    # Windows

    def over(self, partition: Sequence[str], order: Sequence[str]) -> str:
        if not order:
            raise Unsupported("Snowflake window functions need an ORDER BY")
        part = f"PARTITION BY {', '.join(partition)} " if partition else ""
        return f"OVER ({part}ORDER BY {', '.join(order)})"

    def lag(self, x: str, offset: int, default: str, over: str) -> str:
        return x if offset == 0 else f"LAG({x}, {offset}, {default}) {over}"

    def lead(self, x: str, offset: int, default: str, over: str) -> str:
        return x if offset == 0 else f"LEAD({x}, {offset}, {default}) {over}"

    # Relations

    def row_ordinal(self) -> str:
        raise Unsupported(
            "Snowflake tables have no row order, so FETCH and windows over a named table "
            "cannot follow the Lean model's list order (windows run with tie_free=True)"
        )

    def limit_offset(self, offset: int, count: int | None) -> str:
        if count is None:
            return f"LIMIT NULL OFFSET {offset}" if offset else ""
        return f"LIMIT {count} OFFSET {offset}" if offset else f"LIMIT {count}"

    def union_all(self, a: str, b: str) -> str:
        return f"({a}) UNION ALL ({b})"


SNOWFLAKE: Dialect = SnowflakeDialect("snowflake")

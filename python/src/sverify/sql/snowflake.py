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
  interval type (only constants added to a timestamp), so an interval is a
  NUMBER of microseconds, as in Lean: `DATEADD(MICROSECOND, …)` adds one to
  a timestamp and `DATEDIFF(MICROSECOND, …)` (exact for microsecond
  timestamps) subtracts two. A result column cannot be an interval.
* **Strings**: a backslash is an escape character in a quoted literal, so
  it is doubled. Without a collation, strings compare by UTF-8 bytes, which
  is Lean's code point order; `LENGTH`, `POSITION` and `SUBSTR` count
  characters; `POSITION('' IN s)` is 1, as probed (it is not documented).
  Regular expressions are POSIX extended with Perl's `\\d`,
  `\\w` and `\\s` (black boxes in Lean); `REGEXP_INSTR` searches, where
  `REGEXP_LIKE` would match the whole string. `SUBSTR` wraps positions and
  lengths at 32 bits, so they are clamped below 2^31 and raise from 2^32 on.
  `UPPER`, `LOWER` and patterns
  with `\\d`, `\\w` or `\\s` raise on non-ASCII text, where Snowflake's
  tables need not be Rust's (#70).
* **Dates**: `DAYOFWEEK`, `WEEK` and `DATE_TRUNC('WEEK')` depend on the
  session's `WEEK_START` and `WEEK_OF_YEAR_POLICY`, so the SQL uses the ISO
  forms (`DAYOFWEEKISO`, `WEEKISO`) and truncates to Monday itself. There is
  no sub-minute millisecond part: it is `SECOND` and `NANOSECOND` combined.
  `TIMESTAMP_NTZ` stays within the years chrono represents, so `date_part`
  is never NULL for a non-NULL timestamp, as in Lean. `DATEADD(MONTH, …)`
  clamps to the end of a shorter month, as `Time.addMonths` does.
* **Windows**: `LAG`/`LEAD` take the default when the offset leaves the
  partition, as in Lean; `ORDER BY` is required. Tables have no row order
  (no `rowid`), so nothing can stand for Lean's list order, which FETCH and
  ties in a window follow: `row_ordinal` is refused. Windows run with
  `to_sql(..., deterministic=True)`, when the caller knows there are no ties.
* **Aggregates**: `VAR_*` and `STDDEV_*` of doubles use a formula that
  cancels catastrophically, so they are refused; sums of doubles are refused
  as their order is not given.
* **Identifiers** fold to upper case unless quoted; every one is quoted.

The facts behind these are in `characterization/snowflake/facts/`, from the
probes in `characterization/snowflake/probes.json`.
"""

from __future__ import annotations

import datetime as dt
import math
import re
from collections.abc import Sequence
from dataclasses import dataclass

from sverify._plan_read import SUBSTR_MAX
from sverify._support import DUCKDB_ONLY
from sverify.sql.core import Dec, Dialect, Kind, Lst, Unsupported

I64_MIN, I64_MAX = -(2**63), 2**63 - 1
INT32_MAX = 2**31 - 1
NAN = "CAST('NaN' AS FLOAT)"
EPOCH = dt.datetime(1970, 1, 1)

_TYPES: dict[str, str] = {
    "int": "NUMBER(38,0)",
    "float": "FLOAT",
    "time": "TIMESTAMP_NTZ(6)",
    "tod": "TIME(9)",
    "interval": "NUMBER(38,0)",
    "date": "DATE",
    "str": "VARCHAR",
    "bool": "BOOLEAN",
}


@dataclass(frozen=True)
class SnowflakeDialect(Dialect):
    def type_name(self, kind: Kind) -> str:
        if isinstance(kind, Dec):
            return super().type_name(kind)
        if isinstance(kind, Lst):
            raise Unsupported("lists are not yet supported on Snowflake; " + DUCKDB_ONLY)
        return _TYPES[kind]

    def result_kind(self, kind: Kind | None) -> None:
        if kind == "interval":
            raise Unsupported(
                "Snowflake has no interval type, so an interval result column is refused"
            )

    def raise_(self, message: str, dep: str, kind: Kind) -> str:
        """An expression of type `kind` that fails with `message`. Snowflake
        has no RAISE function, but casting a non-numeric (non-boolean) string
        is an error that quotes the string. It depends on `dep` so it cannot
        be folded at compile time, and is NULL when `dep` is. A cast to
        `VARCHAR` never fails, so a string's raise goes through a `NUMBER`
        (probes `eval-cast-raise-varchar`, `eval-raise-varchar-via-number`)."""
        msg = self.str_lit(f"sverify: {message}: ")
        if kind == "str":
            return f"TO_VARCHAR(CAST({msg} || TO_VARCHAR({dep}) AS NUMBER(38,0)))"
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
        return str(i) if i >= 0 else f"({i})"

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
        return str(micros)

    # Integers: exact NUMBER(38,0) arithmetic, then the i64 range check.

    def checked(self, r: str, *, row: bool = True) -> str:
        """`r` if it fits in 64 bits, else an error. Row-level checks go
        with `guards=False`; the one on `SUM` (`row=False`) stays."""
        if row and not self.guards:
            return r
        fail = self.raise_("integer overflow", r, "int")
        return f"IFF({r} BETWEEN {I64_MIN} AND {I64_MAX}, {r}, {fail})"

    def folded(self, r: str, value: int | None) -> str:
        """`r` checked, or the literal `value` when the operands were literals
        and it fits: the check of `1 + 1` is the same 150 bytes every time."""
        if value is not None and I64_MIN <= value <= I64_MAX:
            return self.int_lit(value)
        return self.checked(r)

    def int_add(self, a: str, b: str) -> str:
        x, y = _int_value(a), _int_value(b)
        return self.folded(f"({a} + {b})", None if x is None or y is None else x + y)

    def int_sub(self, a: str, b: str) -> str:
        x, y = _int_value(a), _int_value(b)
        return self.folded(f"({a} - {b})", None if x is None or y is None else x - y)

    def int_mul(self, a: str, b: str) -> str:
        x, y = _int_value(a), _int_value(b)
        return self.folded(f"({a} * {b})", None if x is None or y is None else x * y)

    def int_neg(self, a: str) -> str:
        x = _int_value(a)
        return self.folded(f"(- {a})", None if x is None else -x)

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

    def float_logb(self, x: str, b: str) -> str:
        raise Unsupported("Snowflake's LN is not documented to be C's libm")

    def is_nan(self, x: str) -> str:
        return f"({x} = {NAN})"

    def float_eq(self, a: str, b: str) -> str:
        return f"({a} = {b})"

    def float_lt(self, a: str, b: str) -> str:
        return f"({a} < {b})"

    # Temporal

    def time_add_interval(self, ts: str, iv: str) -> str:
        return f"DATEADD(MICROSECOND, {iv}, {ts})"

    def time_sub_interval(self, ts: str, iv: str) -> str:
        return f"DATEADD(MICROSECOND, - ({iv}), {ts})"

    def time_diff(self, a: str, b: str) -> str:
        return f"DATEDIFF(MICROSECOND, {b}, {a})"

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

    def time_micros(self, ts: str) -> str:
        return f"DATE_PART(EPOCH_MICROSECOND, {ts})"

    def time_part(self, part: str, t: str) -> str:
        # HOUR, SECOND and EXTRACT(NANOSECOND …) take a TIME.
        return self.date_part(part, t)

    def as_time(self, us: str) -> str:
        return f"TO_TIMESTAMP_NTZ({us}, 6)"

    def date_days(self, d: str) -> str:
        return f"DATEDIFF(DAY, CAST('1970-01-01' AS DATE), {d})"

    def date_add_days(self, d: str, n: str) -> str:
        return f"DATEADD(DAY, {n}, {d})"

    def add_months(self, x: str, months: int, kind: Kind) -> str:
        # Clamps to the end of a shorter month, as `Time.addMonths`.
        return f"DATEADD(MONTH, {months}, {x})"

    # Aggregates

    def int_sum(self, v: str) -> str:
        # NUMBER(38,0) sums are exact far beyond 64 bits.
        return f"CAST({self.checked(f'SUM({v})', row=False)} AS NUMBER(38,0))"

    def bit_agg(self, fn: str, v: str, over: str) -> str:
        name = {"bit_and": "BITAND_AGG", "bit_or": "BITOR_AGG", "bit_xor": "BITXOR_AGG"}[fn]
        return f"{name}({v}){over and ' ' + over}"

    def int_avg(self, v: str, over: str) -> str:
        # NUMBER(38,0) sums are exact. Division rounds to a scale, so subtract
        # the remainder (MOD has the dividend's sign) and divide exactly.
        total, n = f"SUM({v}) {over}", f"COUNT({v}) {over}"
        return f"CAST(({total} - MOD({total}, {n})) / {n} AS NUMBER(38,0))"

    def window_int_sum(self, v: str, over: str) -> str:
        return f"CAST({self.checked(f'SUM({v}) {over}', row=False)} AS NUMBER(38,0))"

    def float_var(self, fn: str, v: str) -> str:
        raise Unsupported(
            "Snowflake's VAR_SAMP, VAR_POP and STDDEV of doubles cancel catastrophically "
            "(0 for 1e9 + {4, 7, 13, 16}, whose sample variance is 30), outside the "
            "reference's bounds (upstream/bugs/SF-4.json)"
        )

    def float_sum(self, v: str, o: str) -> str:
        raise Unsupported(
            "Snowflake does not add doubles in a given order, and the rounding of a SUM or "
            "AVG of doubles depends on it"
        )

    # Strings

    def is_ascii(self, s: str) -> str:
        return f"(OCTET_LENGTH(TO_BINARY({s}, 'UTF-8')) = LENGTH({s}))"

    def octet_length(self, s: str) -> str:
        return f"OCTET_LENGTH(TO_BINARY({s}, 'UTF-8'))"

    def greatest(self, a: str, b: str) -> str:
        # Snowflake's `GREATEST` is NULL if any argument is.
        return f"GREATEST_IGNORE_NULLS({a}, {b})"

    def least(self, a: str, b: str) -> str:
        return f"LEAST_IGNORE_NULLS({a}, {b})"

    def like_pattern(self, p: str) -> str:
        # Ends with an odd number of backslashes: a non-backslash (or nothing),
        # then pairs, then one (REGEXP_LIKE matches the whole string).
        odd = f"REGEXP_LIKE({p}, {self.str_lit(r'(.*[^\\])?(\\\\)*\\')}, 's')"
        return f"IFF({odd}, {p} || {self.str_lit(chr(92))}, {p})"

    def substring(self, s: str, start: str, length: str | None) -> str:
        """`SUBSTR` reads its start and length as 32-bit integers, wrapping
        larger ones (upstream/bugs/SF-2.json): a start of 2^32 + 2 is 2, a
        length of 2^31 is negative. No string is 2^31 - 1 characters long
        (128 MiB at most), so anything from there on is clamped to it. From
        2^32 on, outside `Text.substrInRange`, the SQL raises as the other
        engines do. `Lowering.substring` passes a start of at least 1, and a
        length that is the plan's literal or a smaller `GREATEST(…, 0)`: a
        literal of 2^32 or more is refused, so a computed length needs only
        the clamp."""
        if re.fullmatch(r"\d+", start):
            first = self.int32_lit(int(start))
        else:
            # The string is the raise's dependency: `start` is written twice, not three times.
            top = self.int_lit(INT32_MAX)
            if self.guards:
                fail = self.raise_("substring offset outside of supported range", s, "int")
                top = f"IFF({start} >= {SUBSTR_MAX}, {fail}, {top})"
            first = f"LEAST({start}, {top})"
        if length is None:
            return f"SUBSTR({s}, {first})"
        if re.fullmatch(r"\d+", length):
            n = self.int32_lit(int(length))
        else:
            n = f"LEAST({length}, {INT32_MAX})"
        return f"SUBSTR({s}, {first}, {n})"

    @staticmethod
    def int32_lit(k: int) -> str:
        """A literal start or length `k ≥ 0` as SUBSTR reads it."""
        if k >= SUBSTR_MAX:
            raise Unsupported(f"a substring position or length of {k} is not below 2^32")
        return str(min(k, INT32_MAX))

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
            "cannot follow the Lean model's list order (windows run with deterministic=True)"
        )

    def limit_offset(self, offset: int, count: int | None) -> str:
        if count is None:
            return f"LIMIT NULL OFFSET {offset}" if offset else ""
        return f"LIMIT {count} OFFSET {offset}" if offset else f"LIMIT {count}"

    def union_all(self, a: str, b: str) -> str:
        return f"({a}) UNION ALL ({b})"


_INT = re.compile(r"\(?(-?\d+)\)?")


def _int_value(sql: str) -> int | None:
    """The value of an integer literal as `int_lit` writes it, else None."""
    m = _INT.fullmatch(sql)
    return int(m.group(1)) if m else None


SNOWFLAKE: Dialect = SnowflakeDialect("snowflake")

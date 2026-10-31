"""Apache Spark SQL (and Databricks SQL) with the Lean model's semantics.

Targets Spark 4 with the session configuration of `SPARK_CONF`, above all
ANSI mode: without it integer overflow wraps around and a bad cast is NULL,
where the Lean model (and this SQL) raises. Every hook either emits SQL whose
result is the Lean value, checked on a local Spark session by
`tests/test_sql_spark.py`, or raises `Unsupported`. The divergences:

* **Integers** are `BIGINT`. In ANSI mode `+`, `-`, `*`, negation and
  `MIN div -1` raise on overflow. `/` returns a double, so integer division
  is `div`, which truncates; `%` has the sign of the dividend. A literal
  without a cast is an `INT` (or a `DECIMAL` beyond 64 bits), so every
  integer constant is cast. `SUM` of `BIGINT` raises as soon as a partial
  sum overflows, though Lean's is the true total: it adds `DECIMAL(38,0)`
  values instead (exact) and checks the total against 64 bits.
* **Doubles** are IEEE, but in ANSI mode `/` raises on a zero divisor, so
  `x / ±0.0` is spelled out (±inf or NaN by the signs). `CAST(x AS BIGINT)`
  truncates, raises on NaN and ±inf, but saturates at 2⁶³: the range is
  checked first. `FLOOR` and `CEIL` return `BIGINT`, and `ROUND(-0.4)` is
  +0.0, so these keep NaN, ±inf and large values as they are and give a
  zero result the sign of its argument. `POWER` is Java's `Math.pow`,
  which is only within 1 ulp, so double powers are refused.
* **Signed zeros and NaN**: `=` and `<` treat NaN as equal to itself and
  largest, as Lean does for a positive NaN, but -0.0 as equal to +0.0, so
  comparisons go through the core's total order. The sign bit of a zero is
  read from its text (`CAST(-0.0 AS STRING)` is `'-0.0'`). Spark has one
  NaN, read as Lean's +NaN: a negative-NaN literal is refused and negating
  a NaN raises. `GROUP BY`, `DISTINCT` and window partitions normalise
  -0.0 to +0.0 (`NormalizeFloatingNumbers`): the extra sign key keeps the
  groups apart and `group_value` puts the sign back. The optimizer takes the
  literals -0.0 and +0.0 for equal and folds a `CASE` between them into one
  of them, so `case_when` writes such a choice as arithmetic.
* **NULL order**: `NULLS FIRST` is the default for ascending sorts; every
  key says where NULLs go.
* **Timestamps** are `TIMESTAMP_NTZ`: wall-clock microseconds like Lean.
  Plain `TIMESTAMP` is `TIMESTAMP_LTZ` (by `spark.sql.timestampType`), whose
  calendar fields follow the session time zone, and `date_trunc` returns
  one, so truncation is computed on `TIMESTAMP_NTZ` and `DATE` values
  instead and never touches the time zone. Intervals are `INTERVAL DAY TO
  SECOND`, microseconds like Lean. `extract(SECOND …)` is a decimal with the
  microseconds; `WEEK` is ISO, and `dayofweek` counts from Sunday = 1. Spark
  reaches beyond the years chrono represents, so `date_part` is NULL
  outside them, as in Lean.
* **Strings**: string literals take backslash escapes (with
  `spark.sql.parser.escapedStringLiterals` off), so backslashes are
  doubled. Strings compare by UTF-8 bytes under the default collation
  `UTF8_BINARY`, which is Lean's code point order; a column with another
  collation (`UTF8_LCASE`, ICU) would compare differently. `length`,
  `locate` and `substring` count characters. Regular expressions are
  Java's, which agree with Rust's on simple patterns (black boxes in Lean);
  `RLIKE` searches.
* **Decimals** do not occur in the model; the only ones here are the exact
  `DECIMAL(38,0)` sums and `extract(SECOND …)`, cast back to `BIGINT`.
* **Rows**: tables (Parquet, Delta, views) have no row order, so nothing
  can stand for Lean's list order, which FETCH and ties in a sort or window
  follow: `row_ordinal` is refused. Windows and sorts run with
  `to_sql(..., tie_free=True)`, when the caller knows there are no ties.
  Over `VALUES` the order is known, and a `SUM` or `AVG` of doubles adds in
  that order (`aggregate` over the sorted values), as Lean does.
* **Identifiers** are quoted with backticks; `spark.sql.caseSensitive` keeps
  `a` and `A` apart.
"""

from __future__ import annotations

import math
import re
from collections.abc import Sequence
from dataclasses import dataclass

from sverify.sql.core import I64_MAX, I64_MIN, Dialect, Kind, Unsupported, _timestamp_text

#: The timestamps chrono represents (`Time.partMin`, `Time.partMax`): years
#: -262143 to 262142.
YEAR_MIN, YEAR_MAX = -262143, 262142

#: Session settings the SQL relies on; `SparkSession.builder.config` each.
SPARK_CONF: dict[str, str] = {
    # Overflow, division by zero and bad casts raise instead of wrapping or
    # giving NULL.
    "spark.sql.ansi.enabled": "true",
    # Only LTZ values (none here) depend on it; pinned so nothing does.
    "spark.sql.session.timeZone": "UTC",
    "spark.sql.timestampType": "TIMESTAMP_NTZ",
    "spark.sql.caseSensitive": "true",
    # Backslash escapes in string literals, as `str_lit` writes them.
    "spark.sql.parser.escapedStringLiterals": "false",
}

_TYPES: dict[str, str] = {
    "int": "BIGINT",
    "float": "DOUBLE",
    "time": "TIMESTAMP_NTZ",
    "date": "DATE",
    "interval": "INTERVAL DAY TO SECOND",
    "str": "STRING",
    "bool": "BOOLEAN",
}


@dataclass(frozen=True)
class SparkDialect(Dialect):
    def quote(self, ident: str) -> str:
        return "`" + ident.replace("`", "``") + "`"

    def type_name(self, kind: Kind) -> str:
        return _TYPES[kind]

    def raise_(self, message: str, dep: str, kind: Kind) -> str:
        text = f"concat({self.str_lit(f'sverify: {message}: ')}, CAST({dep} AS STRING))"
        fail = self.cast(f"raise_error({text})", kind)
        return f"(CASE WHEN {dep} IS NULL THEN {self.null(kind)} ELSE {fail} END)"

    # Literals

    def str_lit(self, s: str) -> str:
        s = s.replace("\\", "\\\\").replace("'", "\\'")
        # Control characters as escapes, so every query is one line of text.
        return "'" + "".join(f"\\u{ord(c):04x}" if ord(c) < 32 else c for c in s) + "'"

    def float_lit(self, f: float) -> str:
        negative = math.copysign(1.0, f) < 0
        if math.isnan(f) and negative:
            raise Unsupported("Spark has a single NaN; a negative NaN cannot be written")
        if f == 0 and negative:
            return "(- CAST('0' AS DOUBLE))"  # IEEE negation
        return super().float_lit(f)

    def timestamp_lit(self, micros: int) -> str:
        return f"TIMESTAMP_NTZ '{_timestamp_text(micros)}'"

    # Integers: ANSI mode raises on BIGINT overflow.

    def trunc_div(self, a: str, b: str) -> str:
        return f"({a} div {b})"

    def trunc_mod(self, a: str, b: str) -> str:
        return f"({a} % {b})"

    def int_product(self, a: str, n: str) -> str:
        # Partial products grow in magnitude, so the checked `*` raises
        # exactly when the result leaves 64 bits.
        reps = f"array_repeat({a}, CAST({n} AS INT))"
        return f"aggregate({reps}, {self.int_lit(1)}, (acc, e) -> acc * e)"

    # Doubles

    def float_div(self, a: str, b: str) -> str:
        if (c := _float_const(b)) is not None and c != 0:
            return f"({a} / {b})"
        nan, inf, ninf = (self.float_lit(x) for x in (float("nan"), float("inf"), float("-inf")))
        by_zero = (
            f"(CASE WHEN {a} IS NULL THEN {self.null('float')} "
            f"WHEN isnan({a}) OR {a} = 0 THEN {nan} "
            f"WHEN {self.sign_bit(a)} = {self.sign_bit(b)} THEN {inf} ELSE {ninf} END)"
        )
        return f"(CASE WHEN {b} = 0 THEN {by_zero} ELSE {a} / {b} END)"

    def float_neg(self, a: str) -> str:
        fail = self.raise_("negating NaN gives a negative NaN, which Spark lacks", a, "float")
        return f"(CASE WHEN isnan({a}) THEN {fail} ELSE (- {a}) END)"

    def signed(self, r: str, x: str) -> str:
        """`r`, a whole double computed from the finite `x`, with the sign of
        `x` when it is zero (Spark's detour through integers loses it):
        `x * +0.0` is the zero with the sign of `x`."""
        return f"(CASE WHEN {r} = 0 THEN {x} * {self.float_lit(0.0)} ELSE {r} END)"

    def whole(self, fn: str, x: str) -> str:
        """`fn` (FLOOR or CEIL, which return BIGINT) on a double. Doubles of
        magnitude 2⁵² and more are whole already; NaN and ±inf stay."""
        big = self.float_lit(2.0**52)
        value = self.signed(f"CAST({fn}({x}) AS DOUBLE)", x)
        return f"(CASE WHEN isnan({x}) OR abs({x}) >= {big} THEN {x} ELSE {value} END)"

    def float_floor(self, x: str) -> str:
        return self.whole("FLOOR", x)

    def float_ceil(self, x: str) -> str:
        return self.whole("CEIL", x)

    def float_round(self, x: str) -> str:
        # Half away from zero on the shortest decimal of the double, which is
        # the double's own rounding (a halfway double prints as one); only the
        # sign of a zero result is lost.
        return self.signed(f"ROUND({x})", x)

    def float_pow(self, a: str, b: str) -> str:
        raise Unsupported(
            "Spark's POWER is Java's Math.pow, within 1 ulp of the C pow the Lean model uses"
        )

    def float_to_int(self, x: str) -> str:
        # The cast raises on NaN and ±inf but saturates at 2⁶³: check first.
        lo, hi = self.float_lit(-(2.0**63)), self.float_lit(2.0**63)
        fail = self.raise_("CAST to BIGINT out of range", x, "int")
        return f"(CASE WHEN {x} >= {lo} AND {x} < {hi} THEN CAST({x} AS BIGINT) ELSE {fail} END)"

    def is_nan(self, x: str) -> str:
        return f"isnan({x})"

    def case_when(self, c: str, t: str, e: str) -> str:
        """Spark's optimizer takes the literals -0.0 and +0.0 for equal
        (`SimplifyConditionals` compares boxed doubles with `==`), so a
        `CASE` choosing between them becomes one of them. Equal branches
        need no `CASE`; opposite zeros are a product with the condition,
        which no rule folds."""
        if t == e:
            return t
        zeros = {self.float_lit(0.0): False, self.float_lit(-0.0): True}
        if t in zeros and e in zeros:
            neg = self.is_true(c) if zeros[t] else self.not3(self.is_true(c))
            sign = f"(1.0D - 2.0D * CAST({neg} AS DOUBLE))"
            return f"({sign} * {self.float_lit(0.0)})"
        return super().case_when(c, t, e)

    def sign_bit(self, x: str) -> str:
        """`x < 0`, and for a zero its text: Spark's one NaN is +NaN."""
        return f"(CAST({x} AS STRING) LIKE '-%')"

    def float_rank(self, x: str) -> str:
        return f"(CASE WHEN {x} IS NULL THEN NULL WHEN isnan({x}) THEN 1 ELSE 0 END)"

    def group_value(self, x: str, kind: Kind | None) -> str:
        # The GROUP BY normalised -0.0 to +0.0; its sign key did not.
        if kind != "float":
            return x
        neg = self.float_lit(-0.0)
        return f"(CASE WHEN {x} = 0 AND {self.sign_bit(x)} THEN {neg} ELSE {x} END)"

    # Temporal

    def date_part(self, part: str, ts: str) -> str:
        sec = f"extract(SECOND FROM {ts})"
        value = {
            "week": f"extract(WEEK FROM {ts})",
            "dow": f"(dayofweek({ts}) - 1)",
            "doy": f"dayofyear({ts})",
            "second": f"CAST(FLOOR({sec}) AS BIGINT)",
            "millisecond": f"CAST(FLOOR({sec} * 1000) AS BIGINT)",
            "microsecond": f"CAST({sec} * 1000000 AS BIGINT)",
        }.get(part, f"{part}({ts})")
        inside = f"year({ts}) BETWEEN {YEAR_MIN} AND {YEAR_MAX}"
        return f"(CASE WHEN {inside} THEN {self.cast(value, 'int')} END)"

    def date_trunc(self, unit: str, ts: str) -> str:
        # `date_trunc` returns TIMESTAMP_LTZ; these stay in NTZ and DATE.
        sec = f"extract(SECOND FROM {ts})"
        day = f"CAST({ts} AS DATE)"
        match unit:
            case "microsecond":
                return ts
            case "millisecond":
                return f"({ts} - make_dt_interval(0, 0, 0, {sec} - FLOOR({sec} * 1000) / 1000))"
            case "second":
                return f"({ts} - make_dt_interval(0, 0, 0, {sec} - FLOOR({sec})))"
            case "minute":
                return f"({ts} - make_dt_interval(0, 0, 0, {sec}))"
            case "hour":
                return f"({ts} - make_dt_interval(0, 0, minute({ts}), {sec}))"
            case "day":
                return f"CAST({day} AS TIMESTAMP_NTZ)"
            case "week":
                # dayofweek: Sunday 1, Monday 2.
                return f"CAST(date_sub({day}, (dayofweek({ts}) + 5) % 7) AS TIMESTAMP_NTZ)"
        return f"CAST(trunc({day}, {self.str_lit(unit.upper())}) AS TIMESTAMP_NTZ)"

    # Aggregates

    def int_sum(self, v: str) -> str:
        total = f"SUM(CAST({v} AS DECIMAL(38,0)))"
        fail = self.raise_("integer overflow in SUM", total, "int")
        inside = f"{total} BETWEEN {I64_MIN} AND {I64_MAX}"
        return f"(CASE WHEN {inside} THEN CAST({total} AS BIGINT) ELSE {fail} END)"

    def float_sum(self, v: str, o: str) -> str:
        pairs = f"collect_list(named_struct('o', {o}, 'v', {v})) FILTER (WHERE {v} IS NOT NULL)"
        values = f"transform(array_sort({pairs}), p -> p.v)"
        return f"aggregate({values}, {self.float_lit(0.0)}, (acc, x) -> acc + x)"

    # Strings

    def char_length(self, s: str) -> str:
        return f"length({s})"

    def strpos(self, s: str, t: str) -> str:
        return f"locate({t}, {s})"

    def starts_with(self, s: str, t: str) -> str:
        return f"startswith({s}, {t})"

    def ends_with(self, s: str, t: str) -> str:
        return f"endswith({s}, {t})"

    def like_pattern(self, p: str) -> str:
        odd = f"({p} RLIKE {self.str_lit(r'(^|[^\\])(\\\\)*\\$')})"
        return f"(CASE WHEN {odd} THEN concat({p}, {self.str_lit(chr(92))}) ELSE {p} END)"

    def substring(self, s: str, start: str, length: str | None) -> str:
        return (
            f"substring({s}, {start})" if length is None else f"substring({s}, {start}, {length})"
        )

    def regex_search(self, s: str, pattern: str) -> str:
        return f"({s} RLIKE {self.str_lit(pattern)})"

    # Windows

    def over(self, partition: Sequence[str], order: Sequence[str]) -> str:
        if not order:
            raise Unsupported("Spark window functions need an ORDER BY")
        return super().over(partition, order)

    def lag(self, x: str, offset: int, default: str, over: str) -> str:
        return x if offset == 0 else super().lag(x, offset, default, over)

    def lead(self, x: str, offset: int, default: str, over: str) -> str:
        return x if offset == 0 else super().lead(x, offset, default, over)

    # Relations

    def row_ordinal(self) -> str:
        raise Unsupported(
            "Spark tables have no row order, so FETCH and windows over a named table "
            "cannot follow the Lean model's list order (windows run with tie_free=True)"
        )


def _float_const(sql: str) -> float | None:
    """The value of a `float_lit` constant, or None for other SQL."""
    m = re.fullmatch(r"CAST\('([^']*)' AS DOUBLE\)", sql)
    return float(m.group(1)) if m else None


SPARK: Dialect = SparkDialect("spark")

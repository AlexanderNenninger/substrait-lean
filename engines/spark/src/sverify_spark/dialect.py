"""Apache Spark SQL (and Databricks SQL) with the Lean model's semantics.

Targets Spark 4 with the session configuration of `SPARK_CONF`, above all
ANSI mode: without it integer overflow wraps around and a bad cast is NULL,
where the Lean model (and this SQL) raises. Every hook either emits SQL whose
result is the Lean value, checked on a local Spark session by
`engines/spark/tests/test_sql_spark.py`, or raises `Unsupported`. The divergences:

* **Integers** are `BIGINT`. In ANSI mode `+`, `-`, `*`, negation and
  `MIN div -1` raise on overflow. `/` returns a double, so integer division
  is `div`, which truncates; `%` has the sign of the dividend. A literal
  without a cast is an `INT` (or a `DECIMAL` beyond 64 bits), so every
  integer constant is cast. `SUM` of `BIGINT` raises as soon as a partial
  sum overflows, though Lean's is the true total: it adds `DECIMAL(38,0)`
  values instead (exact) and checks the total against 64 bits.
* **Doubles** are IEEE, but in ANSI mode `/` raises on a zero divisor of
  either sign, IEEE division (`on_division_by_zero` = `IEEE`) included: that
  raise is what `sparkBin .fdivIeee` states (ruling 161).
  `CAST(x AS BIGINT)` truncates, raises on NaN and ±inf, but saturates at
  2⁶³: the range is checked first. `FLOOR` and `CEIL` return `BIGINT`, so
  they keep NaN, ±inf and large values as they are. `POWER` is Java's
  `Math.pow`, which is only within 1 ulp, so double powers are refused.
* **Zero and NaN**: `=` and `<` are the model's: NaN equals itself and is
  largest, and -0.0 equals 0.0. `GROUP BY`, `DISTINCT` and window
  partitions treat them the same way (`NormalizeFloatingNumbers`).
* **NULL order**: `NULLS FIRST` is the default for ascending sorts; every
  key says where NULLs go.
* **Timestamps** are `TIMESTAMP_NTZ`: wall-clock microseconds like Lean.
  Plain `TIMESTAMP` is `TIMESTAMP_LTZ` (by `spark.sql.timestampType`), whose
  calendar fields follow the session time zone, and `date_trunc` returns
  one, so truncation is computed on `TIMESTAMP_NTZ` and `DATE` values
  instead and never touches the time zone. Intervals are `INTERVAL DAY TO
  SECOND`, microseconds like Lean. `extract(SECOND …)` is a decimal with the
  microseconds; `WEEK` is ISO, and `dayofweek` counts from Sunday = 1. Spark
  holds timestamps beyond the reference's (years 0 and +10000), so the
  writer raises outside 0001-01-01 to 9999-12-31 before `date_part` (D32).
* **Strings**: string literals take backslash escapes (with
  `spark.sql.parser.escapedStringLiterals` off), so backslashes are
  doubled. Strings compare by UTF-8 bytes under the default collation
  `UTF8_BINARY`, which is Lean's code point order; a column with another
  collation (`UTF8_LCASE`, ICU) would compare differently. `length`,
  `locate` and `substring` count characters. Regular expressions are
  Java's, which agree with Rust's on simple patterns (black boxes in Lean);
  `RLIKE` searches. `upper` and `lower` call the collated form, which does not follow the
  JVM's default locale, and raise on the scalars the engines map differently (D51);
  patterns with `\\d`, `\\w` or `\\s` raise on non-ASCII text, where Java's tables
  differ from Rust's (#70).
* **Decimals** (#27) follow the reference's types, which are Spark's own
  (`DecimalPrecision`) up to 38 digits; past them Spark cuts the scale to no
  less than 6 (`spark.sql.decimalOperations.allowPrecisionLoss`), so a sum
  or product whose type would pass 38 digits at a scale above 6 is refused.
  A smaller scale rounds half away from zero (`ROUND_HALF_UP`), as the
  reference does. `-x` rounds past 34 significant digits (SP-1), so a
  negation of more than 34 digits is `0 - x`, exact up to scale 6 at 38
  digits, and refused past it. A double goes to a decimal as
  `round(x · 10ˢ)` in doubles, through `BIGINT`, since Spark reads a double
  as its shortest text. Division by an integer (an `AVG`) splits the
  quotient exactly and rounds its tail half away from zero (`decimal_div`),
  up to 12 decimal places and 32 integer digits.
* **Rows**: tables (Parquet, Delta, views) have no row order, so nothing
  can stand for Lean's list order, which `to_sql(..., rows="sequence")`
  asks for: `row_ordinal` is refused. Under the default `rows="multiset"`
  ties and the rows of a FETCH are open, as `Rel.Allowed` leaves them, and
  the plan runs.
  A `SUM` or `AVG` of doubles is Spark's own, within the plan's bound of the
  reference's correctly rounded sum (D25, `float_sum`).
* **Identifiers** are quoted with backticks; `spark.sql.caseSensitive` keeps
  `a` and `A` apart.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import ClassVar

from sverify._unsupported import ISSUE_1725
from sverify.sql.core import (
    I64_MAX,
    I64_MIN,
    Dec,
    Dialect,
    GuardIssue,
    Kind,
    Lst,
    Unsupported,
    _timestamp_text,
)

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


def _digits(k: Kind) -> tuple[int, int]:
    """The precision and scale Spark gives an operand of kind `k` in decimal
    arithmetic: a `BIGINT` is a `DECIMAL(20, 0)`."""
    if isinstance(k, Dec):
        return k.p, k.s
    if k == "int":
        return 20, 0
    raise Unsupported(f"decimal arithmetic with a {k} operand on Spark")


@dataclass(frozen=True)
class SparkDialect(Dialect):
    # Decimals (#27), as the module's docstring says.
    decimals: bool = True
    # A `MIN` or `MAX` of mixed zeros depends on order and partitioning
    # (spark-zero-order); its keys are canonical already.
    canonical_zero_reps: ClassVar[frozenset[str]] = frozenset({"extreme"})

    def quote(self, ident: str) -> str:
        return "`" + ident.replace("`", "``") + "`"

    def type_name(self, kind: Kind) -> str:
        if isinstance(kind, Dec):
            return super().type_name(kind)
        if isinstance(kind, Lst):
            if kind.elem is None:
                raise Unsupported("a list whose elements' type is not known")
            return f"ARRAY<{self.type_name(kind.elem)}>"
        if kind == "instant":
            raise self.to_duckdb(
                "Spark has no map for a timestamp with a time zone yet", ISSUE_1725
            )
        if kind not in _TYPES:
            raise self._no_time()
        return _TYPES[kind]

    def time_of_day_lit(self, micros: int) -> str:
        raise self._no_time()

    def _no_time(self) -> Unsupported:
        # `tod`, the one kind `_TYPES` lacks.
        return self.to_duckdb(
            "a time of day (TIME) on Spark: Spark 4.3 reads TIME only with "
            "spark.sql.timeType.enabled on and refuses it by default (spark-time-type)"
        )

    def raise_(self, message: str, dep: str, kind: Kind, issue: GuardIssue) -> str:
        text = f"concat({self.str_lit(f'sverify: {message}: ')}, CAST({dep} AS STRING))"
        fail = self.cast(f"raise_error({text})", kind)
        return f"(CASE WHEN {dep} IS NULL THEN {self.null(kind)} ELSE {fail} END)"

    # Lists (#94)

    def unnest_from(self, source: str, lst: str, alias: str) -> str:
        # `posexplode` counts from 0 and gives no row for a NULL or empty list.
        e, i = self.quote("e"), self.quote("i")
        return (
            f"{source}, LATERAL (SELECT col AS {e}, CAST(pos + 1 AS BIGINT) AS {i} "
            f"FROM (SELECT posexplode({lst}))) AS {alias}"
        )

    def list_lit(self, items: list[str], kind: Lst) -> str:
        return self.cast(f"array({', '.join(items)})", kind)

    def list_element(self, x: str, offset: int) -> str:
        # `try_element_at` counts from 1 and from the end (-1 the last), and gives NULL out
        # of range where `element_at` raises (spark-list-index).
        return f"try_element_at({x}, {offset + 1 if offset >= 0 else offset})"

    def cardinality(self, x: str) -> str:
        return f"cardinality({x})"

    def collect(self, v: str, order: Sequence[str]) -> str:
        if order:
            raise self.refused("array_agg")
        # `collect_list` skips NULLs and gives `[]` for no values, where the model gives NULL.
        return f"(CASE WHEN COUNT({v}) = 0 THEN NULL ELSE collect_list({v}) END)"

    # Literals

    def str_lit(self, s: str) -> str:
        s = s.replace("\\", "\\\\").replace("'", "\\'")
        # Control characters as escapes, so every query is one line of text.
        return "'" + "".join(f"\\u{ord(c):04x}" if ord(c) < 32 else c for c in s) + "'"

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

    def whole(self, fn: str, x: str) -> str:
        """`fn` (FLOOR or CEIL, which return BIGINT) on a double. Doubles of
        magnitude 2⁵² and more are whole already; NaN and ±inf stay."""
        big = self.float_lit(2.0**52)
        value = f"CAST({fn}({x}) AS DOUBLE)"
        return f"(CASE WHEN isnan({x}) OR abs({x}) >= {big} THEN {x} ELSE {value} END)"

    def float_floor(self, x: str) -> str:
        return self.whole("FLOOR", x)

    def float_ceil(self, x: str) -> str:
        return self.whole("CEIL", x)

    def float_round(self, x: str) -> str:
        # Half away from zero on the shortest decimal of the double, which is
        # the double's own rounding (a halfway double prints as one).
        return f"ROUND({x})"

    def float_pow(self, a: str, b: str) -> str:
        raise self.to_duckdb(
            "Spark's POWER is Java's Math.pow, within 1 ulp of the C pow the Lean model uses "
            "(spark-elem-rounding)"
        )

    def float_to_int(self, x: str) -> str:
        # The cast raises on NaN and ±inf but saturates at 2⁶³: check first.
        lo, hi = self.float_lit(-(2.0**63)), self.float_lit(2.0**63)
        fail = self.raise_("CAST to BIGINT out of range", x, "int", "badCast")
        return f"(CASE WHEN {x} >= {lo} AND {x} < {hi} THEN CAST({x} AS BIGINT) ELSE {fail} END)"

    def is_nan(self, x: str) -> str:
        return f"isnan({x})"

    def float_eq(self, a: str, b: str) -> str:
        return f"({a} = {b})"

    def float_lt(self, a: str, b: str) -> str:
        return f"({a} < {b})"

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
        return self.cast(value, "int")

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

    def date_days(self, d: str) -> str:
        return f"CAST(unix_date({d}) AS BIGINT)"

    def date_add_days(self, d: str, n: str) -> str:
        return f"date_add({d}, CAST({n} AS INT))"

    def add_months(self, x: str, months: int, kind: Kind) -> str:
        # `add_months` clamps to the end of a shorter month, as
        # `Time.addMonths` (since Spark 3.0 also from a month's last day).
        if kind == "time":
            return f"({x} + make_ym_interval(0, {months}))"
        return f"add_months({x}, {months})"

    def as_time(self, us: str) -> str:
        # The session time zone is UTC, so the NTZ cast keeps the instant's clock.
        return f"CAST(timestamp_micros({us}) AS TIMESTAMP_NTZ)"

    def time_micros(self, ts: str) -> str:
        # The session time zone is UTC, so the LTZ cast keeps the wall clock.
        return f"unix_micros(CAST({ts} AS TIMESTAMP_LTZ))"

    # Aggregates

    def int_sum(self, v: str) -> str:
        total = f"SUM(CAST({v} AS DECIMAL(38,0)))"
        fail = self.raise_("integer overflow in SUM", total, "int", "sumWraps")
        inside = f"{total} BETWEEN {I64_MIN} AND {I64_MAX}"
        return f"(CASE WHEN {inside} THEN CAST({total} AS BIGINT) ELSE {fail} END)"

    def int_avg(self, v: str, over: str) -> str:
        # An exact DECIMAL(38,0) sum; `div` truncates toward zero.
        total = f"SUM(CAST({v} AS DECIMAL(38,0))) {over}"
        return f"CAST({total} div COUNT({v}) {over} AS BIGINT)"

    def window_int_sum(self, v: str, over: str) -> str:
        total = f"SUM(CAST({v} AS DECIMAL(38,0))) {over}"
        fail = self.raise_("integer overflow in SUM", total, "int", "sumWraps")
        inside = f"{total} BETWEEN {I64_MIN} AND {I64_MAX}"
        return f"(CASE WHEN {inside} THEN CAST({total} AS BIGINT) ELSE {fail} END)"

    def day_interval(self, days: int) -> str:
        return f"INTERVAL {days} DAYS"

    # Decimals

    def decimal_arith(
        self, op: str, a: str, b: str, sa: int, k: Dec, kinds: tuple[Kind, Kind] | None = None
    ) -> str:
        if kinds is None:
            raise Unsupported(f"decimal {op} of operands of unknown types on Spark")
        (p1, s1), (p2, s2) = (_digits(x) for x in kinds)
        if op == "*":
            p, sc = p1 + p2 + 1, s1 + s2
        else:
            sc = max(s1, s2)
            p = max(p1 - s1, p2 - s2) + sc + 1
        if p > 38 and sc > 6:
            # spark-decimal-arith: Spark cuts the scale to fit 38 digits.
            raise Unsupported(
                f"decimal {op} of DECIMAL({p1}, {s1}) and DECIMAL({p2}, {s2}) on Spark: "
                f"its type DECIMAL({p}, {sc}) has more than 38 digits, and Spark rounds it "
                "to fewer decimal places; cast an operand to fewer digits"
            )
        return self.cast(f"({a} {op} {b})", k)

    def decimal_pair(self, what: str, ka: Kind | None, kb: Kind | None) -> None:
        """Spark brings two decimals of different scales (a comparison, `IN`, a join key,
        `GREATEST`, `LEAST`) to the wider type `DECIMAL(max(p₁ - s₁, p₂ - s₂) + max(s₁,
        s₂), max(s₁, s₂))`, and where that has more than 38 digits cuts the scale, which
        rounds the operand of the higher scale: `CAST(2 AS DECIMAL(38,0)) =
        CAST(1.5 AS DECIMAL(38,10))` is true, and `GREATEST` of `1.50` and `1.5000000001`
        is `1.50` (spark-decimal-compare-scale). A pair that fits compares exactly. An
        operand of another or unknown kind (a `NULL` literal) is not checked."""
        if not (isinstance(ka, Dec) or ka == "int") or not (isinstance(kb, Dec) or kb == "int"):
            return
        (p1, s1), (p2, s2) = _digits(ka), _digits(kb)
        wide = max(p1 - s1, p2 - s2) + max(s1, s2)
        if s1 != s2 and wide > 38:
            raise Unsupported(
                f"{what} of DECIMAL({p1}, {s1}) with DECIMAL({p2}, {s2}) on Spark: "
                f"its common type has {wide} digits, and Spark rounds the operand of "
                "the higher scale to fit 38 (spark-decimal-compare-scale); "
                "cast an operand to fewer digits"
            )

    def decimal_neg(self, a: str, k: Dec | None = None) -> str:
        # SP-1: `-x` rounds past 34 significant digits. `0 - x` is exact where
        # its type keeps the scale: up to 37 digits, or 38 at scale 6 or less.
        if k is not None and k.p <= 34:
            return f"(-{a})"
        if k is not None and (k.p <= 37 or k.s <= 6):
            return self.cast(f"({self.decimal_lit(0, Dec(1, 0))} - {a})", k)
        raise self.to_duckdb(
            f"negation of a DECIMAL({k.p if k else '?'}, {k.s if k else '?'}) on Spark: "
            "Spark rounds -x past 34 digits and 0 - x past scale 6 at 38 digits (SP-1)",
            "see #27",
            "cast it to 34 digits or fewer",
        )

    def decimal_abs(self, a: str, k: Dec | None = None) -> str:
        # SP-1: `abs` negates a negative value as `-x` does.
        return f"(CASE WHEN {a} < 0 THEN {self.decimal_neg(a, k)} ELSE {a} END)"

    def decimal_cast(self, a: str, k: Dec, src: Kind | None = None) -> str:
        if src != "float":
            return self.cast(a, k)
        if k.p > 18:
            raise self.to_duckdb(
                f"CAST of a double to DECIMAL({k.p}, {k.s}) on Spark: Spark reads the "
                "double as its shortest text, which past 18 digits is not its value",
                "see #27",
                "cast to 18 digits or fewer",
            )
        # `round(x · 10ˢ)` in doubles, halves away from zero (Spark's `ROUND` of
        # a double rounds its shortest text, which keeps every half where it
        # is); whole doubles below 2⁶³ are exact as `BIGINT`s.
        scale = self.float_lit(float(10**k.s))
        units = self.cast(f"CAST(ROUND({a} * {scale}) AS BIGINT)", Dec(k.p, 0))
        return self.cast(f"({units} * {self.decimal_lit(1, Dec(k.s + 1, k.s))})", k)

    def decimal_to_int(self, a: str) -> str:
        # Truncates toward zero; ANSI raises outside 64 bits.
        return f"CAST({a} AS BIGINT)"

    def decimal_div(self, a: str, b: str, sa: int, k: Dec) -> str:
        """`a / b`, a decimal of scale `sa` by an integer, at scale `k.s`, half
        away from zero (`roundDivInt?`), NULL for `b = 0`. Spark's own quotient
        rounds at a scale of its own first (spark-decimal-arith), so the
        quotient is split exactly: `a = q·b + r` (`%` keeps `a`'s sign), the
        whole part `q = (a - r) / b`, and the rounded tail `t = r·10ᵏ / b`
        as integers below 10³² (`DIV` truncates, so `2R ± b` rounds half away
        from zero). Each step's type stays within what Spark keeps exact."""
        ks, whole = k.s, k.p - k.s
        if ks > 12 or whole > 32 or (k.p > 37 and ks > 6):
            raise self.to_duckdb(
                f"decimal division (an AVG of decimals) to DECIMAL({k.p}, {ks}) on Spark: "
                "past 12 decimal places, 32 integer digits, or 37 digits at more than 6 "
                "places, Spark rounds a step of the exact quotient (spark-decimal-arith)",
                "see #27, after 1.0",
                "cast it to fewer digits",
            )
        n = self.cast(f"NULLIF({b}, 0)", Dec(20, 0))  # `-n` and `2n` past 64 bits
        r = f"({a} % {n})"
        q = self.cast(f"(({a} - {r}) / {n})", Dec(max(whole, 1), 0))
        big = f"({r} * {10**ks})"
        sign = f"CASE WHEN ({big} < 0) <> ({n} < 0) THEN -{n} ELSE {n} END"
        tail = f"((2 * {big} + {sign}) DIV (2 * {n}))"
        tail = self.cast(tail, Dec(ks + 1, 0))
        frac = (
            self.cast(f"({tail} * {self.decimal_lit(1, Dec(ks, ks))})", Dec(ks + 1, ks))
            if ks
            else tail
        )
        return self.cast(f"({q} + {frac})", k)

    def float_lit(self, f: float) -> str:
        # Spark reads the text `-0.0` as a decimal zero (spark-zero-sign): a double
        # literal takes the suffix.
        return "-0.0D" if str(f) == "-0.0" else super().float_lit(f)

    def float_extreme(self, fn: str, v: str, over: str) -> str:
        # NaN is the greatest double, and -0.0 equals 0.0, keeping whichever
        # came first (spark-nan-order, spark-zero-order): the codes' order up
        # to the zero. Which zero depends on row order and partitioning
        # (spark-zero-order), so the class's canonical value stands for it.
        return self.zero_rep(f"{fn}({v}) {over}" if over else f"{fn}({v})", "extreme")

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
            raise self.to_duckdb("Spark window functions need an ORDER BY")
        return super().over(partition, order)

    def lag(self, x: str, offset: int, default: str, over: str) -> str:
        return x if offset == 0 else super().lag(x, offset, default, over)

    def lead(self, x: str, offset: int, default: str, over: str) -> str:
        return x if offset == 0 else super().lead(x, offset, default, over)

    # Relations

    def row_ordinal(self) -> str:
        raise self.no_row_order("Spark")


SPARK: Dialect = SparkDialect("spark")

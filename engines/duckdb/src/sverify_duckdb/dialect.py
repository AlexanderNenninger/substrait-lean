"""The DuckDB dialect.

DuckDB already raises on BIGINT overflow (`+`, `-`, `*` and negation), divides
doubles by IEEE 754 rules, has `isnan`, and numbers a table's rows in insertion
order with `rowid`. Its `=` and `<` on doubles are the model's: NaN equals
itself and is largest, and -0.0 equals 0.0 (D31 keeps the values raw). Its `//` truncates BIGINTs
(and is plain `/` on doubles), so integer division is built from `%`, which
truncates, and is exact whichever way `//` rounds; `error()` raises where
DataFusion fails at run time.

Strings: `length`, `strpos` and `substring` count code points (DuckDB has
`*_grapheme` variants for grapheme clusters), and strings compare bytewise
without a collation. `LIKE` has no escape character by default, so the SQL
names one. Regular expressions are RE2's, DataFusion's Rust's: they agree on
the simple patterns of `Text.simpleRegex`, but `\\d`, `\\w` and `\\s` are
ASCII-only in RE2. `upper`/`lower` map case with utf8proc (black boxes in
Lean; `'ß'` stays one character, where DataFusion writes `'SS'`). So the SQL
raises on non-ASCII text where they would differ from DataFusion (#70).

Where DuckDB computes a function differently from the reference (doubles'
NaN and ±inf, the elementary functions outside their domains, division and
`%` by zero, `MIN % -1`, `<<`, `overflow` = `SILENT` or `SATURATE`), the SQL is
the generated lowering's template, proved in Lean (`lowered`,
`sverify.sql.lowering`, `engines/duckdb/facts/` R15).

Times: `date_part`'s parts mean what they do in DataFusion (`millisecond`
and `microsecond` within the minute, `week` ISO, `dow` from Sunday) on the
proleptic calendar with a year 0. DuckDB's timestamps reach beyond the
reference's (0001-01-01 to 9999-12-31, D32), so the writer raises outside them
before `date_part`, truncation or date arithmetic. Adding months clamps to the
end of the month, as `Time.addMonths` does. The
timestamp 2⁶³ - 1 µs is DuckDB's `infinity` (and its range starts in 290309
BC), which `date_trunc` leaves as it is.
"""

from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction
from typing import ClassVar

from sverify.black_box import BlackBox
from sverify.sql.core import (
    I64_MAX,
    I64_MIN,
    Dec,
    Dialect,
    GuardIssue,
    Kind,
    Lst,
    Unsupported,
    raised_issue,
)


def _order_by(order: Sequence[str]) -> str:
    """` ORDER BY …` of an ordered aggregate, nothing when it has no keys."""
    return f" ORDER BY {', '.join(order)}" if order else ""


@dataclass(frozen=True)
class DuckDBDialect(Dialect):
    # DuckDB computes decimals exactly (#27): `+`, `-` and `×` at the types the
    # reference gives them, casts rounding half away from zero.
    decimals: bool = True
    # DuckDB keeps the zero it read last (duckdb-minmax-zero-sign), also in a key.
    canonical_zero_reps: ClassVar[frozenset[str]] = frozenset({"extreme", "keys"})
    orders_text: bool = True

    def type_name(self, kind: Kind) -> str:
        return "DOUBLE" if kind == "float" else super().type_name(kind)

    def interval_lit(self, micros: int) -> str:
        return f"to_microseconds({self.int_lit(micros)})"

    def interval_micros(self, iv: str) -> str:
        return f"epoch_us({iv})"

    def is_nan(self, x: str) -> str:
        return f"isnan({x})"

    def float_eq(self, a: str, b: str) -> str:
        return f"({a} = {b})"

    def float_lt(self, a: str, b: str) -> str:
        return f"({a} < {b})"

    def raise_(self, message: str, dep: str, kind: Kind, issue: GuardIssue) -> str:
        text = f"concat({self.str_lit(f'sverify: {message}: ')}, CAST({dep} AS VARCHAR))"
        return self.cast(f"error({text})", kind)

    def trunc_div(self, a: str, b: str) -> str:
        # The dividend minus the remainder divides exactly, however `//` rounds. `%`
        # raises on `MIN % -1`, which is where the quotient overflows.
        return f"(({a} - ({a} % {b})) // {b})"

    def trunc_mod(self, a: str, b: str) -> str:
        return f"({a} % {b})"

    def int_product(self, a: str, n: str) -> str:
        return f"list_reduce(list_transform(range({n}), lambda i: {a}), lambda x, y: x * y)"

    def float_to_int(self, x: str) -> str:
        # The cast raises on NaN, ±inf and values outside 64 bits.
        return f"CAST(trunc({x}) AS BIGINT)"

    def float_to_int_or_null(self, x: str) -> str:
        # NULL where `float_to_int` raises: NaN (above every number in
        # DuckDB), ±inf and outside [-2⁶³, 2⁶³), where no double lies within
        # 2048 below -2⁶³. A range test, twice as fast as TRY_CAST.
        lo, hi = "-9223372036854775808.0", "9223372036854775808.0"
        return f"(CASE WHEN {x} >= {lo} AND {x} < {hi} THEN CAST(trunc({x}) AS BIGINT) END)"

    def narrow_or_null(self, x: str, bits: int) -> str:
        lo, hi = self.int_lit(-(2 ** (bits - 1))), self.int_lit(2 ** (bits - 1) - 1)
        return f"(CASE WHEN {x} BETWEEN {lo} AND {hi} THEN {x} END)"

    def lowered(
        self, fn: str, args: list[str], kind: Kind, consts: Sequence[float | int | None] = ()
    ) -> str | None:
        # The generated, proved templates (`engines/duckdb/Sverify/DuckDB/Lowering.lean`).
        from sverify.sql import lowering

        sql = lowering.render(
            fn,
            args,
            lambda message, dep: self.raise_(message, dep, kind, raised_issue(message)),
            self.float_lit,
            self.int_lit,
            self.guards,
            consts,
        )
        # Wrap-arounds compute in HUGEINT: the result is a BIGINT again.
        return self.cast(sql, "int") if sql is not None and kind == "int" else sql

    def float_round(self, x: str) -> str:
        # DuckDB's `ROUND` of a negative value that rounds to zero is `-0.0`, the
        # reference's `0.0`: the proved template (`round_zero_sign`).
        low = self.lowered("Substrait.UnFn.fround", [x], "float")
        return low if low is not None else super().float_round(x)

    def float_ceil(self, x: str) -> str:
        low = self.lowered("Substrait.UnFn.fceil", [x], "float")
        return low if low is not None else super().float_ceil(x)

    def row_ordinal(self) -> str:
        return "rowid"

    @staticmethod
    def _unscaled(x: str, s: int) -> str:
        """The integer `x · 10ˢ` of a decimal of scale `s`, as a HUGEINT, without
        the product (DuckDB's `DECIMAL(38) * 10ˢ` raises where `x` has more
        than `38 - s` integer digits): the integer part, then the fraction."""
        if not s:
            return f"CAST({x} AS HUGEINT)"
        whole = f"CAST(TRUNC({x}) AS HUGEINT) * {10**s}"
        return f"({whole} + CAST(({x} - TRUNC({x})) * {10**s} AS HUGEINT))"

    def decimal_div(self, a: str, b: str, sa: int, k: Dec) -> str:
        """As the base writes it, with the quotient `⌊(2·|u|·10ᵏ + |n|) / 2|n|⌋`
        split as `|u| = q·|n| + r`, so that no product passes 38 digits
        where the result fits (#1497)."""
        u = self._unscaled(a, sa)
        n = f"CAST({b} AS HUGEINT)"
        sign = f"CASE WHEN ({u} < 0) <> ({n} < 0) THEN -1 ELSE 1 END"
        f = 10 ** (k.s - sa)
        mag = (
            f"((ABS({u}) // ABS({n})) * {f} + (2 * (ABS({u}) % ABS({n})) * {f} + ABS({n})) "
            f"// (2 * ABS({n})))"
        )
        q = self.cast(f"({sign} * {mag})", Dec(38, 0))
        scaled = f"{q} * {self.decimal_lit(1, Dec(k.s + 1, k.s))}"
        return self.case_when(f"{n} = 0", self.null(k), self.cast(scaled, k))

    def decimal_compare(self, op: str, a: str, ka: Kind | None, b: str, kb: Kind | None) -> str:
        """Decimals of different scales compared as integers: DuckDB casts both
        sides to one `DECIMAL(38, s)` and raises on a value that does not fit
        (duckdb-decimal-compare-scale, #1498). With `m = 10ᵏ` for the scale
        gap, the low-scale side `L` and the high-scale side `H` as unscaled
        integers: `L·m < H` is `L < ⌊H/m⌋ ∨ (L = ⌊H/m⌋ ∧ H mod m > 0)`,
        `L·m = H` is `L = ⌊H/m⌋ ∧ H mod m = 0`, and `H < L·m` is `⌊H/m⌋ < L`."""

        def scale(k: Kind | None) -> int | None:
            return k.s if isinstance(k, Dec) else 0 if k == "int" else None

        sa, sb = scale(ka), scale(kb)
        if sa is None or sb is None or sa == sb:
            return super().decimal_compare(op, a, ka, b, kb)
        lo_is_a = sa < sb
        (low, sl), (high, sh) = ((a, sa), (b, sb)) if lo_is_a else ((b, sb), (a, sa))
        m = 10 ** (sh - sl)
        ul, uh = self._unscaled(low, sl), self._unscaled(high, sh)
        q = f"({uh} // {m} - CASE WHEN {uh} % {m} < 0 THEN 1 ELSE 0 END)"
        r = f"({uh} - {q} * {m})"
        if op == "eq":
            return f"({ul} = {q} AND {r} = 0)"
        if lo_is_a:  # L·m < H
            return f"({ul} < {q} OR ({ul} = {q} AND {r} > 0))"
        return f"({q} < {ul})"  # H < L·m

    def int_sum(self, v: str) -> str:
        # SUM of BIGINT is a HUGEINT: exact.
        total = f"SUM({v})"
        fail = self.raise_("integer overflow in SUM", total, "int", "sumWraps")
        inside = f"{total} BETWEEN {I64_MIN} AND {I64_MAX}"
        return (
            f"(CASE WHEN {total} IS NULL THEN {self.null('int')} WHEN {inside} "
            f"THEN CAST({total} AS BIGINT) ELSE {fail} END)"
        )

    def int_avg(self, v: str, over: str) -> str:
        # SUM of BIGINT is a HUGEINT, so the sum is exact; `//` truncates.
        return f"CAST(SUM({v}) {over} // COUNT({v}) {over} AS BIGINT)"

    def window_int_sum(self, v: str, over: str) -> str:
        # SUM of BIGINT is a HUGEINT: exact.
        total = f"SUM({v}) {over}"
        fail = self.raise_("integer overflow in SUM", total, "int", "sumWraps")
        inside = f"{total} BETWEEN {I64_MIN} AND {I64_MAX}"
        return (
            f"(CASE WHEN {total} IS NULL THEN {self.null('int')} WHEN {inside} "
            f"THEN CAST({total} AS BIGINT) ELSE {fail} END)"
        )

    def float_extreme(self, fn: str, v: str, over: str) -> str:
        # DuckDB orders doubles as the codes do: NaN above `+∞` (#371). Of equal
        # zeros it keeps the one it read last (duckdb-minmax-zero-sign): the
        # class's canonical value stands for it.
        return self.zero_rep(f"{fn}({v}) {over}" if over else f"{fn}({v})", "extreme")

    def pick(self, fn: str, v: str, order: Sequence[str]) -> str:
        # DuckDB's own `first`/`last` of the non-NULL values: the group's
        # values are not gathered into a list (4x faster on 5M rows, #810).
        return f"{fn}({v}{_order_by(order)}) FILTER (WHERE {v} IS NOT NULL)"

    def window_pick(self, fn: str, v: str, w: str) -> str:
        return f"{'FIRST' if fn == 'first' else 'LAST'}_VALUE({v} IGNORE NULLS) {w}"

    def string_agg(self, v: str, sep: str, order: Sequence[str]) -> str:
        return f"string_agg({v}, {sep}{_order_by(order)})"

    def collect(self, v: str, order: Sequence[str]) -> str:
        return f"list({v}{_order_by(order)}) FILTER (WHERE {v} IS NOT NULL)"

    def quantile(self, cont: bool, v: str, q: str) -> str:
        # DuckDB reads a decimal fraction exactly (#53). Its `RN = (n - 1)·q`
        # is a double and its interpolation `lo·(1 - d) + hi·d` rounds, so
        # `QUANTILE_CONT` leaves the model's neighbours in two places
        # (`duckdb-quantile-cont-interpolation`, #900):
        # - where the exact position is whole and its double is not, it
        #   interpolates toward the next value: the written plan takes
        #   `quantile_disc`, whose index `⌈n·q⌉ - 1` is the whole position
        #   (the decimal `q` is read exactly) and so the model's neighbour;
        # - where the lower neighbour is the first value, the weight rounds
        #   and the result can pass the upper neighbour, which the clamp to
        #   `[MIN, MAX]` does not catch below the maximum: the second
        #   smallest value, `min(x, 2)[2]`, bounds it.
        # The guards read `COUNT` and the decimal `q` in integers. A dyadic
        # `q` needs none: its double position is exact.
        # Elsewhere `RN`'s double is within `(n - 1)·2^-51` of the exact
        # position `P`. Outside the band `d·2^51 <= (n - 1)·den`, with `d`
        # the distance of `P` to the nearest whole position, its floor and
        # ceiling are the exact ones and the clamp keeps the result between
        # the neighbours. In the band (whole positions included) the engine's
        # pair holds the nearest whole position `m`, and the written plan
        # takes `quantile_disc` of `q` moved by 10^-15 toward 1/2: its index
        # `⌈n·q'⌉ - 1` is `m` for `n <= 10^14` (the decimal is read exactly,
        # `duckdb-quantile-cont-interpolation`). Past that count it raises.
        # Between -inf and +inf the interpolation is NaN, which no operation
        # creates (#561): raise where it is NaN and no value is (NaN sorts
        # above every number, so `MAX` is NaN exactly then). In the band the
        # same cases are the neighbours `s[k] = -inf`, `s[k + 1] = +inf` at a
        # fractional position, counted below.
        if not cont:
            return f"quantile_disc({v}, {q})"
        qc = f"quantile_cont({v}, {q})"
        value = f"LEAST(GREATEST({qc}, MIN({v})), MAX({v}))"
        frac = Fraction(q)
        num, den = frac.numerator, frac.denominator
        dyadic = den & (den - 1) == 0
        n1 = f"CAST(COUNT({v}) - 1 AS HUGEINT)"
        if not dyadic:
            first = f"({n1} * {num} < {den})"
            value = self.case_when(first, f"LEAST({value}, ({self.second_smallest(v)}))", value)
        fail = self.raise_("domain error", f"MIN({v})", "float", "domain")
        if self.guards:
            made = f"({self.is_nan(qc)} AND NOT {self.is_nan(f'MAX({v})')})"
            value = self.case_when(made, fail, value)
        if dyadic:
            return value
        scale = next(s for s in range(1000) if (frac * 10**s).denominator == 1)
        if scale > 21:
            raise Unsupported(
                f"quantile fraction {q} has {scale} decimals; DuckDB's quantile writes "
                "at most 21 (#900), use a shorter fraction"
            )
        shifted = frac + (Fraction(1, 10**15) if 2 * num < den else -Fraction(1, 10**15))
        digits = max(scale, 15)
        disc = f"quantile_disc({v}, 0.{int(shifted * 10**digits):0{digits}d})"
        rest = f"({n1} * {num} % {den})"
        if self.guards:
            k = f"({n1} * {num} // {den})"
            inf = "CAST('inf' AS DOUBLE)"
            opposite = (
                f"({rest} <> 0 AND COUNT(*) FILTER (WHERE {v} = -{inf}) = {k} + 1"
                f" AND COUNT(*) FILTER (WHERE {v} < {inf}) = {k} + 1"
                f" AND COUNT(*) FILTER (WHERE {v} = {inf}) > 0)"
            )
            disc = self.case_when(opposite, fail, disc)
        band = f"(LEAST({rest}, {den} - {rest}) <= {n1} * {den} // {2**51})"
        value = self.case_when(band, disc, value)
        # An engine limit the reference does not have, so a `guard_free`
        # report cannot prove it absent: it is written with `guards=False`
        # too, like integer `SUM`'s check and `finite`.
        beyond = f"({n1} >= {10**14})"
        raise_ = self.raise_(
            "quantile count beyond 10^14", f"COUNT({v})", "float", "quantilePosition"
        )
        return self.case_when(beyond, raise_, value)

    def second_smallest(self, v: str) -> str:
        """The second value of the column `v` in order, NULLs skipped."""
        return f"min({v}, 2)[2]"

    def mode(self, v: str, order: Sequence[str]) -> str:
        # Its input in this order, DuckDB keeps the value seen first of those
        # that tie (`engines/duckdb/facts/duckdb-mode-ties.json`).
        return f"mode({v} ORDER BY {', '.join(order)})"

    def unnest_from(self, source: str, lst: str, alias: str) -> str:
        e, i = self.quote("e"), self.quote("i")
        return f"{source}, UNNEST({lst}) WITH ORDINALITY AS {alias}({e}, {i})"

    def list_lit(self, items: list[str], kind: Lst) -> str:
        if not items:
            return self.cast("[]", kind)
        return self.cast(f"[{', '.join(items)}]", kind)

    def list_element(self, x: str, offset: int) -> str:
        # DuckDB counts from 1, and from the end (-1 the last) like the model.
        return f"({x})[{offset + 1 if offset >= 0 else offset}]"

    def cardinality(self, x: str) -> str:
        return f"len({x})"

    def list_fn(self, name: str, args: list[str]) -> str:
        # DuckDB's own, as the model states them (#810, #812).
        return f"{name}({', '.join(args)})"

    def pair(self, a: str, b: str) -> str:
        return f"(CASE WHEN {a} IS NULL OR {b} IS NULL THEN NULL ELSE list_value({a}, {b}) END)"

    def covar(self, fn: str, v: str) -> str:
        return f"{fn.upper()}({v}[1], {v}[2])"

    def is_ascii(self, s: str) -> str:
        return f"(strlen({s}) = length({s}))"

    def octet_length(self, s: str) -> str:
        return f"strlen({s})"

    def like_pattern(self, p: str) -> str:
        odd = f"regexp_matches({p}, {self.str_lit(r'(^|[^\\])(\\\\)*\\$')})"
        return f"(CASE WHEN {odd} THEN {p} || {self.str_lit(chr(92))} ELSE {p} END)"

    def list_lt(self, a: str, b: str) -> str:
        # DuckDB orders a NULL element above every value; the reference makes
        # the comparison NULL where such an element decides it. `k` is the
        # first position where the elements are distinct (NULL equals NULL).
        k = (
            f"list_position(list_transform(range(1, least(len({a}), len({b})) + 1), "
            f"lambda i: {a}[i] IS DISTINCT FROM {b}[i]), true)"
        )
        return (
            f"(CASE WHEN {a} IS NULL OR {b} IS NULL THEN NULL "
            f"WHEN {k} IS NULL THEN len({a}) < len({b}) "
            f"WHEN {a}[{k}] IS NULL OR {b}[{k}] IS NULL THEN NULL ELSE {a}[{k}] < {b}[{k}] END)"
        )

    def substring(self, s: str, start: str, length: str | None) -> str:
        return (
            f"substring({s}, {start})" if length is None else f"substring({s}, {start}, {length})"
        )

    def trim(self, s: str, chars: str, left: bool, right: bool) -> str:
        f = "trim" if left and right else "ltrim" if left else "rtrim"
        return f"{f}({s}, {chars})"

    def regex_search(self, s: str, pattern: str) -> str:
        return f"regexp_matches({s}, {self.str_lit(pattern)})"

    def regex_extract(self, s: str, pattern: str, group: int) -> str:
        return f"regexp_extract({s}, {self.str_lit(pattern)}, {group})"

    def regex_replace(self, s: str, pattern: str, replacement: str, every: bool) -> str:
        flags = ", 'g'" if every else ""
        return f"regexp_replace({s}, {self.str_lit(pattern)}, {self.str_lit(replacement)}{flags})"

    def black_box(self, row: BlackBox, args: list[str]) -> str:
        # DuckDB's own function: the black box is pinned to it (#325).
        return row.duckdb.format(*args)

    def black_box_agg(self, row: BlackBox, v: str) -> str:
        return row.duckdb.format(v)

    def date_part(self, part: str, ts: str) -> str:
        return self.cast(f"date_part({self.str_lit(part)}, {ts})", "int")

    def day_part(self, part: str, d: str) -> str:
        # A DATE's own parts, which are its midnight's: no cast.
        if part in ("hour", "minute", "second", "millisecond", "microsecond"):
            return super().day_part(part, d)
        return self.cast(f"date_part({self.str_lit(part)}, {d})", "int")

    def date_trunc(self, unit: str, ts: str) -> str:
        return ts if unit == "microsecond" else f"date_trunc({self.str_lit(unit)}, {ts})"

    def time_micros(self, ts: str) -> str:
        return f"epoch_us({ts})"

    def time_add(self, t: str, micros: int) -> str:
        # TIME + INTERVAL wraps around midnight (`duckdb-time-plus-interval`).
        return f"({t} + {self.interval_lit(micros)})"

    def time_trunc(self, unit: str, t: str) -> str:
        # DuckDB has no `date_trunc` of a TIME: truncate it on 1970-01-01.
        return self.cast(self.date_trunc(unit, f"(DATE '1970-01-01' + {t})"), "tod")

    def as_time(self, us: str) -> str:
        return f"make_timestamp({us})"

    def date_time(self, d: str) -> str:
        return f"CAST({d} AS TIMESTAMP)"

    def to_instant(self, ts: str) -> str:
        # By the microseconds, so that no session zone is read (duckdb-instant-conversion).
        return f"make_timestamptz(epoch_us({ts}))"

    def to_naive(self, instant: str) -> str:
        return f"make_timestamp(epoch_us({instant}))"

    def epoch_us(self, ts: str) -> str:
        return f"epoch_us({ts})"

    def date_add_days(self, d: str, n: str) -> str:
        # DATE + INTEGER is a DATE; a count beyond 32 bits leaves chrono's
        # dates anyway (and the cast raises).
        return f"({d} + CAST({n} AS INTEGER))"

    def add_months(self, x: str, months: int, kind: Kind) -> str:
        # DuckDB clamps to the month's end; DATE + INTERVAL is a TIMESTAMP.
        return self.cast(f"({x} + to_months({self.int_lit(months)}))", kind)


DUCKDB: Dialect = DuckDBDialect("duckdb")

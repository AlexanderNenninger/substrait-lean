"""The DuckDB dialect.

DuckDB already raises on BIGINT overflow (`+`, `-`, `*` and negation), divides
doubles by IEEE 754 rules, has `isnan` and `signbit`, and numbers a table's
rows in insertion order with `rowid`. Its `=` and `<` on doubles treat NaN as
equal to itself and largest, but -0.0 as equal to +0.0 and -NaN as NaN, so
comparisons go through the core's total order. Its `//` truncates BIGINTs
(and is plain `/` on doubles), so integer division is built from `%`, which
truncates, and is exact whichever way `//` rounds; `error()` raises where
DataFusion fails at run time.

Strings: `length`, `strpos` and `substring` count code points (DuckDB has
`*_grapheme` variants for grapheme clusters), and strings compare bytewise
without a collation. `LIKE` has no escape character by default, so the SQL
names one. Regular expressions are RE2's, DataFusion's Rust's: they agree on
the simple patterns of `Text.simpleRegex`, but `\\d`, `\\w` and `\\s` are
ASCII-only in RE2. `upper`/`lower` map case with utf8proc (black boxes in
Lean; `'ß'` stays one character, where DataFusion writes `'SS'`).

Times: `date_part`'s parts mean what they do in DataFusion (`millisecond`
and `microsecond` within the minute, `week` ISO, `dow` from Sunday) on the
proleptic calendar with a year 0. DuckDB's timestamps reach beyond the years
chrono represents, so `date_part` is NULL outside them, as in Lean. The
timestamp 2⁶³ - 1 µs is DuckDB's `infinity` (and its range starts in 290309
BC), which `date_trunc` leaves as it is.
"""

from dataclasses import dataclass

from sverify.sql.core import I64_MAX, I64_MIN, Dialect, Kind

#: The timestamps chrono represents (`Time.partMin`, `Time.partMax`).
PART_MIN, PART_MAX = -8334601228800000000, 8210266876799999999


@dataclass(frozen=True)
class DuckDBDialect(Dialect):
    def type_name(self, kind: Kind) -> str:
        return "DOUBLE" if kind == "float" else super().type_name(kind)

    def interval_lit(self, micros: int) -> str:
        return f"to_microseconds({self.int_lit(micros)})"

    def is_nan(self, x: str) -> str:
        return f"isnan({x})"

    def sign_bit(self, x: str) -> str:
        return f"signbit({x})"

    def raise_(self, message: str, dep: str, kind: Kind) -> str:
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

    def row_ordinal(self) -> str:
        return "rowid"

    def int_sum(self, v: str) -> str:
        # SUM of BIGINT is a HUGEINT: exact.
        total = f"SUM({v})"
        fail = self.raise_("integer overflow in SUM", total, "int")
        inside = f"{total} BETWEEN {I64_MIN} AND {I64_MAX}"
        return (
            f"(CASE WHEN {total} IS NULL THEN {self.null('int')} WHEN {inside} "
            f"THEN CAST({total} AS BIGINT) ELSE {fail} END)"
        )

    def float_sum(self, v: str, o: str) -> str:
        values = f"list({v} ORDER BY {o}) FILTER (WHERE {v} IS NOT NULL)"
        start = self.cast("0", "float")
        return f"list_reduce(list_prepend({start}, {values}), lambda x, y: x + y)"

    def char_length(self, s: str) -> str:
        return f"length({s})"

    def strpos(self, s: str, t: str) -> str:
        return f"strpos({s}, {t})"

    def ends_with(self, s: str, t: str) -> str:
        return f"suffix({s}, {t})"

    def like_pattern(self, p: str) -> str:
        odd = f"regexp_matches({p}, {self.str_lit(r'(^|[^\\])(\\\\)*\\$')})"
        return f"(CASE WHEN {odd} THEN {p} || {self.str_lit(chr(92))} ELSE {p} END)"

    def substring(self, s: str, start: str, length: str | None) -> str:
        return (
            f"substring({s}, {start})" if length is None else f"substring({s}, {start}, {length})"
        )

    def trim(self, s: str, chars: str, left: bool, right: bool) -> str:
        f = "trim" if left and right else "ltrim" if left else "rtrim"
        return f"{f}({s}, {chars})"

    def regex_search(self, s: str, pattern: str) -> str:
        return f"regexp_matches({s}, {self.str_lit(pattern)})"

    def date_part(self, part: str, ts: str) -> str:
        us = f"epoch_us({ts})"
        inside = f"{us} BETWEEN {self.int_lit(PART_MIN)} AND {self.int_lit(PART_MAX)}"
        value = self.cast(f"date_part({self.str_lit(part)}, {ts})", "int")
        return f"(CASE WHEN {inside} THEN {value} END)"

    def date_trunc(self, unit: str, ts: str) -> str:
        return ts if unit == "microsecond" else f"date_trunc({self.str_lit(unit)}, {ts})"


DUCKDB: Dialect = DuckDBDialect("duckdb")

"""The DuckDB dialect.

DuckDB already raises on BIGINT overflow (`+`, `-`, `*` and negation), divides
doubles by IEEE 754 rules, has `isnan`, and numbers a table's rows in insertion
order with `rowid`. Its `=` and `<` on doubles are the model's: NaN equals
itself and is largest, and -0.0 equals 0.0 (`canon` keeps -0.0 out of
results). Its `//` truncates BIGINTs
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
`sverify.sql.lowering`, `characterization/duckdb/facts/` R15).

Times: `date_part`'s parts mean what they do in DataFusion (`millisecond`
and `microsecond` within the minute, `week` ISO, `dow` from Sunday) on the
proleptic calendar with a year 0. DuckDB's timestamps reach beyond the years
chrono represents, so `date_part` is NULL outside them, as in Lean, and date
arithmetic raises outside them, where DataFusion fails. Adding months clamps
to the end of the month, as `Time.addMonths` does. The
timestamp 2⁶³ - 1 µs is DuckDB's `infinity` (and its range starts in 290309
BC), which `date_trunc` leaves as it is.
"""

from collections.abc import Sequence
from dataclasses import dataclass

from sverify.black_box import BlackBox
from sverify.sql.core import I64_MAX, I64_MIN, Dialect, Kind, Lst

#: The timestamps chrono represents (`Time.partMin`, `Time.partMax`).
PART_MIN, PART_MAX = -8334601228800000000, 8210266876799999999


@dataclass(frozen=True)
class DuckDBDialect(Dialect):
    # DuckDB computes decimals exactly (#27): `+`, `-` and `×` at the types the
    # reference gives them, casts rounding half away from zero.
    decimals: bool = True

    def type_name(self, kind: Kind) -> str:
        return "DOUBLE" if kind == "float" else super().type_name(kind)

    def interval_lit(self, micros: int) -> str:
        return f"to_microseconds({self.int_lit(micros)})"

    def is_nan(self, x: str) -> str:
        return f"isnan({x})"

    def float_eq(self, a: str, b: str) -> str:
        return f"({a} = {b})"

    def float_lt(self, a: str, b: str) -> str:
        return f"({a} < {b})"

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

    def float_to_int_or_null(self, x: str) -> str:
        # NULL where `float_to_int` raises: NaN (above every number in
        # DuckDB), ±inf and outside [-2⁶³, 2⁶³), where no double lies within
        # 2048 below -2⁶³. A range test, twice as fast as TRY_CAST.
        lo, hi = "-9223372036854775808.0", "9223372036854775808.0"
        return f"(CASE WHEN {x} >= {lo} AND {x} < {hi} THEN CAST(trunc({x}) AS BIGINT) END)"

    def narrow_or_null(self, x: str, bits: int) -> str:
        lo, hi = self.int_lit(-(2 ** (bits - 1))), self.int_lit(2 ** (bits - 1) - 1)
        return f"(CASE WHEN {x} BETWEEN {lo} AND {hi} THEN {x} END)"

    def lowered(self, fn: str, args: list[str], kind: Kind) -> str | None:
        # The generated, proved templates (`SubstraitLean/LoweringDuckDB.lean`).
        from sverify.sql import lowering

        sql = lowering.render(
            fn,
            args,
            lambda message, dep: self.raise_(message, dep, kind),
            self.float_lit,
            self.int_lit,
            self.guards,
        )
        # Wrap-arounds compute in HUGEINT: the result is a BIGINT again.
        return self.cast(sql, "int") if sql is not None and kind == "int" else sql

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

    def int_avg(self, v: str, over: str) -> str:
        # SUM of BIGINT is a HUGEINT, so the sum is exact; `//` truncates.
        return f"CAST(SUM({v}) {over} // COUNT({v}) {over} AS BIGINT)"

    def window_int_sum(self, v: str, over: str) -> str:
        # SUM of BIGINT is a HUGEINT: exact.
        total = f"SUM({v}) {over}"
        fail = self.raise_("integer overflow in SUM", total, "int")
        inside = f"{total} BETWEEN {I64_MIN} AND {I64_MAX}"
        return (
            f"(CASE WHEN {total} IS NULL THEN {self.null('int')} WHEN {inside} "
            f"THEN CAST({total} AS BIGINT) ELSE {fail} END)"
        )

    def window_float_sum(self, v: str, over: str) -> str:
        # The frame's values in frame order (its ORDER BY), folded from 0.0.
        values = f"list({v}) FILTER (WHERE {v} IS NOT NULL) {over}"
        start = self.cast("0", "float")
        return f"list_reduce(list_prepend({start}, {values}), lambda x, y: x + y)"

    def window_float_var(self, sample: bool, sqrt: bool, v: str, over: str) -> str:
        values = f"list({v}) FILTER (WHERE {v} IS NOT NULL) {over}"
        start = self.cast("0", "float")
        n = f"COUNT({v}) {over}"
        total = f"list_reduce(list_prepend({start}, {values}), lambda x, y: x + y)"
        mean = f"({total} / {self.cast(n, 'float')})"
        devs = f"list_transform({values}, lambda x: (x - {mean}) * (x - {mean}))"
        sq = f"list_reduce(list_prepend({start}, {devs}), lambda x, y: x + y)"
        div = self.cast(f"({n} - 1)" if sample else n, "float")
        var = f"GREATEST({sq} / {div}, {start})"
        return f"sqrt({var})" if sqrt else var

    def float_sum(self, v: str, o: str) -> str:
        values = f"list({v} ORDER BY {o}) FILTER (WHERE {v} IS NOT NULL)"
        start = self.cast("0", "float")
        return f"list_reduce(list_prepend({start}, {values}), lambda x, y: x + y)"

    def float_extreme(self, fn: str, v: str, over: str) -> str:
        # DuckDB orders doubles as the codes do: NaN above `+∞` (#371).
        return f"{fn}({v}) {over}" if over else f"{fn}({v})"

    def pick(self, fn: str, v: str, order: Sequence[str]) -> str:
        values = f"list({v} ORDER BY {', '.join(order)}) FILTER (WHERE {v} IS NOT NULL)"
        return f"({values})[{1 if fn == 'first' else -1}]"

    def string_agg(self, v: str, sep: str, order: Sequence[str]) -> str:
        return f"string_agg({v}, {sep} ORDER BY {', '.join(order)})"

    def collect(self, v: str, order: Sequence[str]) -> str:
        return f"list({v} ORDER BY {', '.join(order)}) FILTER (WHERE {v} IS NOT NULL)"

    def quantile(self, cont: bool, v: str, q: str) -> str:
        # DuckDB reads a decimal fraction exactly (#53). Its interpolation
        # `lo·(1−d) + hi·d` may round past the values: the model keeps it
        # between them, and so does the clamp. Between -inf and +inf it is
        # NaN, which no operation creates (#561): raise where it is NaN and
        # no value is (NaN sorts above every number, so `MAX` is NaN exactly
        # then) (`duckdb-quantile-cont-interpolation`).
        if not cont:
            return f"quantile_disc({v}, {q})"
        qc = f"quantile_cont({v}, {q})"
        value = f"LEAST(GREATEST({qc}, MIN({v})), MAX({v}))"
        if not self.guards:
            return value
        made = f"({self.is_nan(qc)} AND NOT {self.is_nan(f'MAX({v})')})"
        return self.case_when(made, self.raise_("domain error", f"MIN({v})", "float"), value)

    def mode(self, v: str, order: Sequence[str]) -> str:
        # Its input in this order, DuckDB keeps the value seen first of those
        # that tie (`characterization/duckdb/facts/duckdb-mode-ties.json`).
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
        us = f"epoch_us({ts})"
        inside = f"{us} BETWEEN {self.int_lit(PART_MIN)} AND {self.int_lit(PART_MAX)}"
        value = self.cast(f"date_part({self.str_lit(part)}, {ts})", "int")
        return f"(CASE WHEN {inside} THEN {value} END)"

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

    def date_add_days(self, d: str, n: str) -> str:
        # DATE + INTEGER is a DATE; a count beyond 32 bits leaves chrono's
        # dates anyway (and the cast raises).
        return f"({d} + CAST({n} AS INTEGER))"

    def add_months(self, x: str, months: int, kind: Kind) -> str:
        # DuckDB clamps to the month's end; DATE + INTERVAL is a TIMESTAMP.
        return self.cast(f"({x} + to_months({self.int_lit(months)}))", kind)


DUCKDB: Dialect = DuckDBDialect("duckdb")

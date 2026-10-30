"""The DuckDB dialect.

DuckDB already raises on BIGINT overflow (`+`, `-`, `*` and negation), divides
doubles by IEEE 754 rules, has `isnan` and `signbit`, and numbers a table's
rows in insertion order with `rowid`. Its `=` and `<` on doubles treat NaN as
equal to itself and largest, but -0.0 as equal to +0.0 and -NaN as NaN, so
comparisons go through the core's total order. Its `//` floors, so integer
division is built from `%`, which truncates; `error()` raises where
DataFusion fails at run time.
"""

from dataclasses import dataclass

from sverify.sql.core import Dialect, Kind


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
        # `//` floors; the dividend minus the remainder divides exactly. `%`
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


DUCKDB: Dialect = DuckDBDialect("duckdb")

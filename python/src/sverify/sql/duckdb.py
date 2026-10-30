"""The DuckDB dialect.

DuckDB already raises on BIGINT overflow (`+`, `-`, `*` and negation), divides
doubles by IEEE 754 rules, has `isnan` and `signbit`, and numbers a table's
rows in insertion order with `rowid`. Its `=` and `<` on doubles treat NaN as
equal to itself and largest, but -0.0 as equal to +0.0 and -NaN as NaN, so
comparisons go through the core's total order.
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

    def row_ordinal(self) -> str:
        return "rowid"


DUCKDB: Dialect = DuckDBDialect("duckdb")

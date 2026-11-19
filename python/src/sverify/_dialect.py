"""Where the reference reads a DuckDB SQL text differently from DuckDB (#1484, D54).

`sv.verify(sql)` reads the text as DuckDB's and the functions as the
reference's. The reference gives a value DuckDB does not in the fields of
`Profile` below, and the report lists each place the lift read one of them
(`Report.dialect_differences`). The raises of the reference (`domain_error`,
`log_zero`) are not here: a raise is visible and the inferred preconditions
name its inputs.

One table, keyed by the `Profile` field. `tests/test_dialect_differences.py`
derives the key set from `REFERENCE` and `DUCKDB` and fails when a field joins
it with no row.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class DialectDifference:
    """A construct of the SQL text whose reference reading differs from DuckDB's."""

    key: str
    """The `Profile` field the lift read: `float_to_int`, `decimal_to_int` or
    `corr_degenerate`."""
    construct: str
    """The construct as written."""
    where: str
    """`"the query"`, or the SQL condition the construct is in."""
    here: str
    """What the reference does."""
    dialect: str
    """What DuckDB does."""
    example: str
    """One input with both values."""
    spellings: str
    """Spellings that mean the same under both semantics, if there are any."""

    def __str__(self) -> str:
        out = (
            f"{self.construct} in {self.where}: {self.here} here, "
            f"{self.dialect} on DuckDB ({self.example})"
        )
        return f"{out}; {self.spellings}" if self.spellings else out


#: Each `Profile` field's entry: how the two readings differ, with an example
#: and the spellings that lift under the reference and mean the same on both.
TABLE: dict[str, dict[str, str]] = {
    "float_to_int": {
        "here": "truncates toward zero",
        "dialect": "rounds to nearest, ties to even",
        "example": "CAST(1.5 AS BIGINT) is 1 here and 2 on DuckDB",
        "spellings": (
            "CAST(round(x) AS BIGINT), CAST(floor(x) AS BIGINT) and "
            "CAST(ceil(x) AS BIGINT) mean the same on both"
        ),
    },
    "decimal_to_int": {
        "here": "truncates toward zero",
        "dialect": "rounds half away from zero",
        "example": "CAST(2.5::DECIMAL(2, 1) AS BIGINT) is 2 here and 3 on DuckDB",
        "spellings": (
            "round, floor and ceil of a DECIMAL are not lifted yet; "
            "CAST(round(CAST(d AS DOUBLE)) AS BIGINT) means the same on both, through a double"
        ),
    },
    "corr_degenerate": {
        "here": "NULL",
        "dialect": "NaN",
        "example": "corr over one pair, or a side whose values are all equal",
        "spellings": "",
    },
}


def difference(key: str, construct: str, where: str = "the query") -> DialectDifference:
    """The entry for `key`, at `construct`."""
    return DialectDifference(key, construct, where, **TABLE[key])

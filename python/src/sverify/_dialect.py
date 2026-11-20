"""Where the reference reads a DuckDB SQL text differently from DuckDB (#1484, D54).

`sv.verify(sql)` reads the text as DuckDB's and the functions as the
reference's. The reference gives a value DuckDB does not in the fields of
`Profile` below. The lift refuses the casts (`REFUSED`, with a hint) and the
report lists `corr` (`Report.dialect_differences`). The raises of the reference (`domain_error`,
`log_zero`) are not here: a raise is visible and the inferred preconditions
name its inputs.

One table, keyed by the `Profile` field. `tests/test_dialect_differences.py`
derives the key set from `PORTABLE` and `DUCKDB` and fails when a field joins
it neither refused nor listed.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class DialectDifference:
    """A construct of the SQL text whose reference reading differs from DuckDB's."""

    key: str
    """The `Profile` field the lift read: `float_to_int` or `corr_degenerate`."""
    construct: str
    """The construct's category, as `UnsupportedError.construct` spells it:
    `function corr`, `CAST`."""
    sql: str
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
            f"{self.sql} in {self.where}: {self.here} here, "
            f"{self.dialect} on DuckDB ({self.example})"
        )
        return f"{out}; {self.spellings}" if self.spellings else out


#: The `Profile` fields the lift refuses under the reference instead of listing
#: (D54, the user's choice on #1484): the message names the spellings that lift for
#: the source type and mean the same under both semantics.
REFUSED: dict[str, str] = {
    "float_to_int": (
        "write CAST(round(x) AS BIGINT), CAST(floor(x) AS BIGINT) or CAST(ceil(x) AS BIGINT), "
        "which mean the same on both"
    ),
}

#: Each `Profile` field the lift lists: how the two readings differ, with an
#: example and the spellings that mean the same.
TABLE: dict[str, dict[str, str]] = {
    "corr_degenerate": {
        "here": "NULL",
        "dialect": "NaN",
        "example": "corr over one pair, or a side whose values are all equal",
        "spellings": "",
    },
}


def difference(key: str, construct: str, sql: str, where: str = "the query") -> DialectDifference:
    """The entry for `key`, at the construct `construct` that the SQL `sql` writes."""
    return DialectDifference(key, construct, sql, where, **TABLE[key])

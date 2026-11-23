"""Where the reference reads a DuckDB SQL text differently from DuckDB (#1484, D54).

`sv.verify(sql)` reads the text as DuckDB's and the functions as the
reference's. The reference gives a value DuckDB does not in the fields of
`Profile` below. The report lists `corr`, `list_contains` and the order of lists, BETWEEN
included (`Report.dialect_differences`).
The raises of the reference (`domain_error`, `log_zero`) and of DuckDB (`min_mod_neg_one`,
listed as a guard's issue) are not here: a raise is visible and the inferred preconditions name
its inputs.

One table, keyed by the `Profile` field. `tests/test_dialect_differences.py`
derives the key set from `PORTABLE` and `DUCKDB` and fails when a field joins
it not listed.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class DialectDifference:
    """A construct of the SQL text whose reference reading differs from DuckDB's."""

    key: str
    """The `Profile` field the lift read, or a `NATIVE` key: `float_to_int`, `corr_degenerate` or
    `list_contains_null_needle` or `list_null_order`."""
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


#: The listed differences that are no `Profile` field: DuckDB's own reading of a construct differs
#: from the plan's under every semantics, at the engine versions named (D54, ruling 208).
NATIVE: frozenset[str] = frozenset({"list_contains_null_needle", "list_null_order"})

#: Each `Profile` field the lift lists: how the two readings differ, with an
#: example and the spellings that mean the same.
TABLE: dict[str, dict[str, str]] = {
    "corr_degenerate": {
        "here": "NULL",
        "dialect": "NaN",
        "example": "corr over one pair, or a side whose values are all equal",
        "spellings": "",
    },
    "list_contains_null_needle": {
        "here": "NULL",
        "dialect": "FALSE (2.0.1; NULL at 2.0.0)",
        "example": "list_contains([], NULL), the empty list and a needle that is NULL",
        "spellings": "a needle that is not NULL, or list_contains(l, x) with x tested for NULL",
    },
    "list_null_order": {
        "here": "NULL",
        "dialect": "TRUE",
        "example": "a NULL element decides the order ([1,2] < [1,NULL,3])",
        "spellings": "",
    },
}


def difference(key: str, construct: str, sql: str, where: str = "the query") -> DialectDifference:
    """The entry for `key`, at the construct `construct` that the SQL `sql` writes."""
    return DialectDifference(key, construct, sql, where, **TABLE[key])

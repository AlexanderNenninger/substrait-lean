"""Black-box functions (#325): DuckDB functions the checker treats as opaque.

Internal: not part of sverify's public API.

The table is `SubstraitLean/BlackBox.lean`'s; this module mirrors it for the
lift (`sverify.sql_lift.blackbox`) and the SQL writers
(`sverify.sql.core.black_box`), and adds what Lean does not need: the SQL
DuckDB computes each function with. `tests/test_black_box.py` checks that the
two tables agree (`substrait-check --black-boxes`).

A row gives a function's name (DuckDB's, and the Substrait extension
function's, under `URN`), its argument and result types, how it treats NULL,
whether it may raise, and its laws: properties of the result the contract
checker uses, which hold of the model by construction and are checked on
random data against DuckDB.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

#: The URN of sverify's black-box functions (`BlackBox.blackBoxUrn`).
URN = "extension:io.sverify:black_box"

Ty = Literal["int", "double", "str", "bool", "date", "atom", "doubles", "ints", "any"]
"""`atom` is an integer, string or boolean (`BlackBox.Ty.atom`); `doubles` and
`ints` are lists of them."""

#: The code of `1.0` (`BlackBox.codeOne`).
CODE_ONE = 2 * 2**1074 + 1

#: A law of the result: `("non_null",)`, `("at_least", k)` or `("at_most", k)`.
#: Bounds of a double are on its code (`SubstraitLean/Float.lean`): `0` is
#: `+0.0`.
Law = tuple[str] | tuple[str, int]


@dataclass(frozen=True)
class BlackBox:
    """A row of the table (`BlackBox.Scalar`, `BlackBox.Aggregate`)."""

    name: str
    kind: Literal["scalar", "aggregate"]
    args: tuple[Ty, ...]
    result: Ty
    duckdb: str
    """DuckDB's SQL, with `{0}`, `{1}`, … for the arguments (an aggregate's
    one argument is the column of its values)."""
    strict: bool = True
    """NULL in, NULL out (a scalar's)."""
    raises: bool = False
    """May raise, on some non-NULL arguments (a scalar's)."""
    laws: tuple[Law, ...] = ()
    empty: float | int | str | bool | None = None
    """An aggregate's result without values (NULLs are skipped)."""


#: The table, in `SubstraitLean/BlackBox.lean`'s order (scalars, then
#: aggregates): each row's anchor is 700 plus its index.
TABLE: tuple[BlackBox, ...] = (
    BlackBox("base64", "scalar", ("str",), "str", "base64(encode({0}))", laws=(("non_null",),)),
    BlackBox(
        "printf",
        "scalar",
        ("str", "atom"),
        "str",
        "printf({0}, {1})",
        raises=True,
        laws=(("non_null",),),
    ),
    BlackBox(
        "format",
        "scalar",
        ("str", "atom"),
        "str",
        "format({0}, {1})",
        raises=True,
        laws=(("non_null",),),
    ),
    BlackBox(
        "octet_length",
        "scalar",
        ("str",),
        "int",
        "octet_length(encode({0}))",
        laws=(("non_null",), ("at_least", 0)),
    ),
    BlackBox(
        "strlen", "scalar", ("str",), "int", "strlen({0})", laws=(("non_null",), ("at_least", 0))
    ),
    BlackBox("signbit", "scalar", ("double",), "bool", "signbit({0})", laws=(("non_null",),)),
    BlackBox(
        "yearweek",
        "scalar",
        ("date",),
        "int",
        # NULL where DuckDB raises (`BlackBox.yearweekMin`).
        "(CASE WHEN {0} >= DATE '5877641-01-04 (BC)' THEN yearweek({0}) END)",
        laws=(("at_least", -587764053), ("at_most", 588158053)),
    ),
    # The vector functions of lists of doubles (#327); `array_*` are the same
    # functions (`sql_lift.blackbox`).
    BlackBox(
        "list_cosine_similarity",
        "scalar",
        ("doubles", "doubles"),
        "double",
        "list_cosine_similarity({0}, {1})",
        raises=True,
        laws=(("at_least", -CODE_ONE),),
    ),
    BlackBox(
        "list_cosine_distance",
        "scalar",
        ("doubles", "doubles"),
        "double",
        "list_cosine_distance({0}, {1})",
        raises=True,
        laws=(("at_least", 0),),
    ),
    BlackBox(
        "list_distance",
        "scalar",
        ("doubles", "doubles"),
        "double",
        "list_distance({0}, {1})",
        raises=True,
        laws=(("non_null",), ("at_least", 0)),
    ),
    BlackBox(
        "list_inner_product",
        "scalar",
        ("doubles", "doubles"),
        "double",
        "list_inner_product({0}, {1})",
        raises=True,
        laws=(("non_null",),),
    ),
    BlackBox(
        "list_negative_inner_product",
        "scalar",
        ("doubles", "doubles"),
        "double",
        "list_negative_inner_product({0}, {1})",
        raises=True,
        laws=(("non_null",),),
    ),
    BlackBox(
        "array_cross_product",
        "scalar",
        ("doubles", "doubles"),
        "doubles",
        # DuckDB's is a DOUBLE[3]; the model's a list.
        "CAST(array_cross_product({0}, {1}) AS DOUBLE[])",
        raises=True,
        laws=(("non_null",),),
    ),
    # A BIGINT, which raises past its range: DuckDB's own is a HUGEINT.
    BlackBox("list_sum", "scalar", ("ints",), "int", "CAST(list_sum({0}) AS BIGINT)", raises=True),
    BlackBox(
        "entropy",
        "aggregate",
        ("any",),
        "double",
        "entropy({0})",
        laws=(("non_null",), ("at_least", 0)),
        empty=0.0,
    ),
)

SCALARS: dict[str, BlackBox] = {b.name: b for b in TABLE if b.kind == "scalar"}
AGGREGATES: dict[str, BlackBox] = {b.name: b for b in TABLE if b.kind == "aggregate"}
NAMES = frozenset(SCALARS) | frozenset(AGGREGATES)


def refusal(name: str, engine: str) -> str:
    """Why `engine` refuses the black box `name`: only DuckDB has them yet."""
    return f"the black box {name} is not yet supported on {engine}; see #271"

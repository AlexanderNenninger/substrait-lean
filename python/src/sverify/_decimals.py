"""The reference's decimal types (#27, #731): the `(precision, scale)` of a
decimal operation's result, as `Parse.decimalCall` and `Measure.kind` type it.

`+` and `-` are exact at the larger scale with one more integer digit, `×` at
the sum of the scales, `SUM` has ten more digits, `AVG` four more digits and
decimal places, and values brought to one type (`CASE`, `COALESCE`, `IN`)
take the most integer digits and the largest scale. A precision is at most
38 digits. The Ibis producer, the SQL writer, the Polars engine and the
incremental views read the rules here, and the SQL lift its common type. The
lift's arithmetic types are DuckDB's (`sverify.sql_lift`), its own semantics.

Internal: not part of sverify's public API (`docs/stability.md`); it may
change in any release.
"""

from __future__ import annotations

from collections.abc import Iterable
from decimal import Context, Decimal

#: The most digits a decimal has (DuckDB's and the model's).
MAX_DIGITS = 38

#: A context past 38 digits and any scale, in which nothing a decimal holds rounds.
#: Python's default context rounds to 28 digits.
EXACT = Context(prec=100)


def scaled(value: Decimal | int | str, exp: int) -> Decimal:
    """`value` times `10 ** exp`, exactly (`Decimal.scaleb` rounds to 28 digits)."""
    return EXACT.scaleb(Decimal(value), exp)


type Digits = tuple[int, int]
"""A decimal type as `(precision, scale)`."""


def capped(p: int, s: int) -> Digits:
    """`(p, s)` with the precision at most `MAX_DIGITS`."""
    return min(MAX_DIGITS, p), s


def add(a: Digits, b: Digits) -> Digits:
    """The type of `a + b` and `a - b`: the larger scale, one more integer digit."""
    (p1, s1), (p2, s2) = a, b
    s = max(s1, s2)
    return capped(max(p1 - s1, p2 - s2) + s + 1, s)


def mul(a: Digits, b: Digits) -> Digits:
    """The type of `a × b`: `p1 + p2 + 1` digits at the sum of the scales."""
    (p1, s1), (p2, s2) = a, b
    return capped(p1 + p2 + 1, s1 + s2)


def mod(a: Digits, b: Digits) -> Digits | None:
    """The type of `a % b` (D62): the larger scale and the fewer integer digits, as the
    remainder is smaller than either operand. None where an operand at the larger scale
    needs more than 38 digits, which the reference refuses."""
    (p1, s1), (p2, s2) = a, b
    s = max(s1, s2)
    if max(p1 - s1, p2 - s2) + s > MAX_DIGITS:
        return None
    return min(p1 - s1, p2 - s2) + s, s


def sum_of(a: Digits) -> Digits:
    """The type of a decimal `SUM`: ten more digits (`Measure.kind`)."""
    return capped(a[0] + 10, a[1])


def avg_of(a: Digits) -> Digits:
    """The type of a decimal `AVG`: four more digits and decimal places
    (`decimalAvgs`)."""
    return capped(a[0] + 4, a[1] + 4)


def common(ds: Iterable[Digits]) -> Digits:
    """The type decimals are brought to as one value: the most integer digits
    and the largest scale."""
    ds = list(ds)
    s = max(s for _, s in ds)
    return capped(max(p - s0 for p, s0 in ds) + s, s)

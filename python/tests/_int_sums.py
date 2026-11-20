"""Sums and means of integer-valued doubles with `Σ |x| <= 2^53` (D35,
amended 2026-11-19; #1608 12b-1): every engine's `SUM` is the exact sum and
its `AVG` the exact mean rounded once. The engine tests
(`engines/*/tests/test_*int_sums*.py`) run these cases; they are the
evidence for the amendment's exactness on each engine's `sum_order` rows."""

import random
from fractions import Fraction

#: Lengths around DuckDB's vector size (2048) and its constant runs.
LENGTHS = (1, 2, 2047, 2048, 2049, 4097, 100_000)


def cases() -> list[tuple[str, list[int]]]:
    rng = random.Random(12)
    out: list[tuple[str, list[int]]] = [
        ("edge", [2**52, 2**52]),
        ("edge-negative", [-(2**52), -(2**52)]),
        ("cancel", [2**51, -(2**51), 2**51, 1]),
        ("third", [1, 1, 1]),
    ]
    for n in LENGTHS:
        out.append((f"constant-{n}", [7] * n))
        hi = (2**53) // n
        out.append((f"random-{n}", [rng.randint(-hi, hi) for _ in range(n)]))
    return out


def check(values: list[int], total: float, mean: float) -> None:
    """The engine's `SUM` is the exact sum and its `AVG` the correctly
    rounded mean."""
    assert sum(abs(v) for v in values) <= 2**53
    s = sum(values)
    assert total == float(s) and Fraction(total) == s, (s, total)
    assert mean == float(Fraction(s, len(values))), (s, len(values), mean)

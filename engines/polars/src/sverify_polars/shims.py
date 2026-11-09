"""The shims of the translation from the reference to Polars (#444).

Internal: `polars_engine` uses them; not part of sverify's public API.

A plan verified under the reference runs on Polars natively wherever Polars
2.1.0 already gives a value the reference allows. Where Polars gives another
value on inputs the reference does not raise on, the translation writes a
shim: one small function here per value choice of the reference that Polars
lacks (`docs/core-semantics.md`, "Obligations, option by option", and its
Polars example). Each shim is a row of `SHIMS`, named as its Lean lemma
(`Polars.<name>`), with the option it discharges and the engine fact that
says what Polars does natively (`engines/polars/facts/`).

Polars's error-side differences (wrapping integers, `NULL` for a zero
divisor, NaN from `inf - inf`) need no shim: the reference raises there, so a
verified plan never reaches them. Where a precondition is checked on the data
(`Report.assumed`), a guard raises before Polars's value is used: the flags
of `GUARDS`, one per issue of `SubstraitLean/Safety.lean`, by its
`Issue.name`.
"""

from __future__ import annotations

from dataclasses import dataclass

import polars as pl

I64_MIN, I64_MAX = -(2**63), 2**63 - 1


@dataclass(frozen=True)
class Shim:
    """One value choice of the reference that Polars makes differently."""

    name: str
    """The Python function and the Lean lemma (`Polars.<name>`)."""
    option: str
    """The option it discharges (`core/Sverify/Core/Options.lean`)."""
    reference: str
    """The reference's choice."""
    polars: str
    """What Polars 2.1.0 does natively."""
    fact: str
    """The fact that records it (`engines/polars/facts/<fact>.json`)."""
    cost: str
    """`argument`: a written argument, free at run time; `expression`: extra
    per-row or per-group expressions."""


@dataclass(frozen=True)
class Guard:
    """A precondition checked on the data, where Polars answers and the
    reference raises."""

    issue: str
    """The issue's `Issue.name` (`SubstraitLean/Safety.lean`)."""
    flag: str
    """The function here that flags the rows or groups it hits."""
    polars: str
    """What Polars gives instead of raising."""
    fact: str


SHIMS: tuple[Shim, ...] = (
    Shim("null_order", "null_order", "as the key states; NULLS_LAST for UNSPECIFIED (D8)",
         "NULLS_FIRST in both directions", "polars-null-order", "argument"),
    Shim("tie_order", "tie_order", "ANY; Rel.eval keeps input order",
         "undocumented without maintain_order", "polars-sort-stability", "argument"),
    Shim("round_half_away", "rounding", "TIE_AWAY_FROM_ZERO (fp.round)",
         "TIE_TO_EVEN", "polars-round", "argument"),
    Shim("int_div_trunc", "division_type", "TRUNCATE", "FLOOR",
         "polars-int-divide", "expression"),
    Shim("int_mod_trunc", "division_type", "TRUNCATE (the dividend's sign)",
         "FLOOR (the divisor's sign)", "polars-int-modulus", "expression"),
    Shim("sum_empty_null", "empty_group_aggregates", "NULL for no values",
         "0 (sum0)", "polars-sum-int", "expression"),
    Shim("avg_int_declared", "avg_int_result", "DECLARED_TYPE: the exact mean, truncated",
         "Float64 mean", "polars-avg-int", "expression"),
    Shim("one_zero", "zero_sign", "ONE_ZERO, also as a group key: on read and after each "
         "operation that can give -0.0", "IEEE: -0.0 kept; a group's key is its first zero",
         "polars-zero-sign", "expression"),
    Shim("strpos_chars", "negative_start", "1-based characters, 0 when absent",
         "str.find: 0-based bytes, NULL when absent", "polars-strpos", "expression"),
    Shim("substring_wrap", "negative_start", "WRAP_FROM_END",
         "str.slice: a negative offset counts from the end, by characters",
         "polars-substring", "expression"),
    Shim("decimal_round_half_away", "decimal_rescale",
         "TIE_AWAY_FROM_ZERO: a cast to a smaller scale; a product at scale s1 + s2",
         "TIE_TO_EVEN, and a product at scale max(s1, s2)", "polars-decimal-casts",
         "expression"),
    Shim("decimal_div_half_away", "decimal_rescale",
         "TIE_AWAY_FROM_ZERO: AVG at scale s + 4, sverify_decimal_div",
         "mean is a Float64; / rounds half to even", "polars-decimal-arith", "expression"),
    Shim("max_nan_greatest", "nan_order", "GREATEST: MAX of a group with a NaN is NaN",
         "IGNORED: min and max skip NaN unless every value is NaN", "polars-min-max-nan",
         "expression"),
)  # fmt: skip

GUARDS: tuple[Guard, ...] = (
    Guard("overflow", "int_overflows", "wraps (two's complement)", "polars-int-arith"),
    Guard("overflow", "div_overflows", "MIN // -1 wraps to MIN", "polars-int-divide"),
    Guard("division by zero", "zero_divisor", "NULL", "polars-int-divide"),
    Guard("SUM overflow", "sum_leaves_i64", "wraps", "polars-sum-int"),
    Guard("domain error", "sum_makes_nan", "NaN from +inf and -inf",
          "polars-nonfinite-aggregates"),
    Guard("overflow to infinity", "makes_infinite", "±inf (IEEE)", "polars-double-arith"),
    Guard("domain error", "fractional_power_of_negative",
          "x ** 0.5 is sqrt(x): NaN for -inf, where IEEE pow gives +inf", "polars-double-arith"),
)  # fmt: skip


# --- Sorts ---------------------------------------------------------------------

#: `(descending, nulls_last)` per Substrait direction. Polars puts NULLs first
#: in both directions by default (polars-null-order), so every key states its
#: placement. An `UNSPECIFIED` direction (or none: protobuf's JSON leaves the
#: default out) is the model's default `SortKey`: ascending, NULLs last (D8).
SORT_DIRECTIONS: dict[str | None, tuple[bool, bool]] = {
    "SORT_DIRECTION_ASC_NULLS_FIRST": (False, False),
    "SORT_DIRECTION_ASC_NULLS_LAST": (False, True),
    "SORT_DIRECTION_DESC_NULLS_FIRST": (True, False),
    "SORT_DIRECTION_DESC_NULLS_LAST": (True, True),
    "SORT_DIRECTION_UNSPECIFIED": (False, True),
    None: (False, True),
}


def null_order(direction: str | None) -> tuple[bool, bool] | None:
    """`(descending, nulls_last)` for a sort key's direction; None for one the
    reference has no order for (`CLUSTERED`)."""
    return SORT_DIRECTIONS.get(direction)


#: Ties keep their input order, as `Rel.eval`'s stable `mergeSort` does. The
#: reference leaves the order of ties open (`tie_order = ANY`), so this is
#: only needed where the plan's result depends on it (a `FETCH` after the
#: sort, D10); it is written on every sort, so reruns agree.
TIE_ORDER = {"maintain_order": True}


def tie_order() -> dict[str, bool]:
    return dict(TIE_ORDER)


# --- Doubles -------------------------------------------------------------------


def one_zero(e: pl.Expr) -> pl.Expr:
    """`-0.0` as `0.0` (`zero_sign = ONE_ZERO`). Not `e + 0.0`: eager Polars
    skips adding a zero."""
    return pl.when(e == 0.0).then(pl.lit(0.0, pl.Float64)).otherwise(e)


def round_half_away(e: pl.Expr) -> pl.Expr:
    """`ROUND` to an integer, halves away from zero (`roundMag`); Polars's
    default rounds them to even (polars-round)."""
    return e.round(0, mode="half_away_from_zero")


def makes_infinite(y: pl.Expr, *xs: pl.Expr) -> pl.Expr:
    """Do the finite doubles `xs` give the `±∞` `y` (`BinFn.infIssue`, #575)?
    NULL for NULL."""
    finite = xs[0].is_finite()
    for x in xs[1:]:
        finite = finite & x.is_finite()
    return finite & y.is_infinite()


def fractional_power_of_negative(x: pl.Expr, y: pl.Expr) -> pl.Expr:
    """A negative base, `-inf` included, to a finite power that is not a
    whole number: the reference's domain error for `power`. Polars computes
    `x ** 0.5` as `sqrt(x)`, NaN for `-inf` (IEEE's `pow` gives `+inf`), so
    the guard covers that input too (`Polars.fractional_power_of_negative`,
    `SubstraitLean/PolarsShims.lean`)."""
    return (x < 0.0) & y.is_finite() & (y.floor() != y)


# --- Integers ------------------------------------------------------------------


def int_div_trunc(a: pl.Expr, b: pl.Expr) -> pl.Expr:
    """The quotient truncated toward zero (`Int.tdiv`). Polars's `//` floors
    (polars-int-divide): one more where the remainder is not zero and the
    signs differ. Native on `Int64` and `Int128` alike."""
    q = a // b
    return pl.when((a % b != 0) & ((a < 0) != (b < 0))).then(q + 1).otherwise(q)


def int_mod_trunc(a: pl.Expr, b: pl.Expr) -> pl.Expr:
    """The remainder with the dividend's sign (`Int.tmod`). Polars's `%` takes
    the divisor's (polars-int-modulus): take `b` off where they differ.
    `MIN % -1` is 0 in both."""
    r = a % b
    return pl.when((r != 0) & ((r < 0) != (a < 0))).then(r - b).otherwise(r)


def int_overflows(a: pl.Expr, b: pl.Expr, op: str) -> pl.Expr:
    """Does `a op b` leave 64 bits (`Issue.wraps`)? Polars wraps instead
    (polars-int-arith); the check runs on 128 bits."""
    x, y = a.cast(pl.Int128), b.cast(pl.Int128)
    w = {"add": x + y, "subtract": x - y, "multiply": x * y}[op]
    return (w < I64_MIN) | (w > I64_MAX)


def div_overflows(a: pl.Expr, b: pl.Expr) -> pl.Expr:
    """`MIN / -1`, which Polars wraps to `MIN` (`Issue.overflow`)."""
    return (a == I64_MIN) & (b == -1)


def zero_divisor(a: pl.Expr, b: pl.Expr) -> pl.Expr:
    """A zero divisor of a value that is not NULL (`Issue.divByZero`); Polars
    gives NULL."""
    return a.is_not_null() & b.eq(0)


# --- Decimals ------------------------------------------------------------------
#
# On unscaled values, `Int128`s of at most 38 digits; Polars's `Int128`
# arithmetic wraps silently, so each step stays within 128 bits.


def _i128(n: int) -> pl.Expr:
    return pl.lit(n, pl.Int128)


def decimal_round_half_away(u: pl.Expr, k: int) -> pl.Expr:
    """The unscaled decimal `u` brought to a scale `k ≥ 1` digits smaller,
    halves away from zero (`decimal_rescale = TIE_AWAY_FROM_ZERO`,
    `roundDiv10`); Polars's cast rounds them to even (polars-decimal-arith).
    `|u| + 5·10ᵏ⁻¹ < 1.5·10³⁸` fits 128 bits."""
    q = (u.abs() + _i128(5 * 10 ** (k - 1))) // _i128(10**k)
    return pl.when(u < 0).then(_i128(0) - q).otherwise(q)


def decimal_div_half_away(x: pl.Expr, n: pl.Expr, k: int) -> tuple[pl.Expr, pl.Expr]:
    """`x · 10ᵏ / n` rounded half away from zero (`roundDivInt?`), for the
    unscaled decimal `x`, an integer `n ≠ 0` (64 bits) and `k ≤ 18`; Polars's
    division rounds to even (polars-decimal-arith). With `|x| = a·|n| + b`,
    the quotient is `a·10ᵏ + ⌊(2b·10ᵏ + |n|) / 2|n|⌋`, and `2b·10ᵏ < 2⁶⁴·10¹⁸`
    fits 128 bits. The second value flags an `a ≥ 10³⁸⁻ᵏ`, whose quotient has
    more than 38 digits (and would leave 128 bits)."""
    an = n.abs()
    an = pl.when(an == 0).then(_i128(1)).otherwise(an)
    ax = x.abs()
    a, b = ax // an, ax % an
    bad = a >= _i128(10 ** (38 - k))
    q = pl.when(bad).then(_i128(0)).otherwise(a) * _i128(10**k) + (_i128(2 * 10**k) * b + an) // (
        _i128(2) * an
    )
    return pl.when((x < 0) != (n < 0)).then(_i128(0) - q).otherwise(q), bad


# --- Strings -------------------------------------------------------------------


def strpos_chars(s: pl.Expr, t: pl.Expr) -> pl.Expr:
    """`Text.strpos`: the 1-based character position of the first `t` in `s`,
    0 where there is none, 1 for an empty `t`. Polars's `str.find` counts
    bytes from 0 and is NULL where `t` is absent (polars-strpos); the
    characters before the first `t` are the first part of a split."""
    before = s.str.split(t).list.first().str.len_chars().cast(pl.Int64)
    found = s.str.find(t, literal=True)
    return (
        pl.when(s.is_null() | t.is_null())
        .then(None)
        .when(t == "")
        .then(pl.lit(1, pl.Int64))
        .when(found.is_null())
        .then(pl.lit(0, pl.Int64))
        .otherwise(before + 1)
    )


def substring_wrap(start: pl.Expr, s: pl.Expr) -> pl.Expr:
    """`Text.substrWrap`'s start: a negative one counts from the end of `s`, in
    characters (`negative_start = WRAP_FROM_END`), as a 1-based position for
    `Text.substr`. Polars's own negative offsets are 0-based from the end and
    clip differently (polars-substring), so the start is rewritten."""
    length = s.str.len_chars().cast(pl.Int64)
    return pl.when(start < 0).then(start + length + 1).otherwise(start)


# --- Aggregates ----------------------------------------------------------------


def sum_empty_null(total: pl.Expr, values: pl.Expr) -> pl.Expr:
    """`SUM` of no values is NULL; Polars's `sum` is 0 (polars-sum-int,
    polars-sum-float). `values` is the aggregated column, NULLs not counted."""
    return pl.when(values.count() == 0).then(None).otherwise(total)


def int_sum(values: pl.Expr) -> pl.Expr:
    """The exact `SUM` of integers, on 128 bits, NULL for no values. Its
    result fits 64 bits unless `sum_leaves_i64`. (A cast of 128-bit values
    is none: Polars drops it.)"""
    return sum_empty_null(values.cast(pl.Int128).sum(), values)


def sum_leaves_i64(total: pl.Expr) -> pl.Expr:
    """Does a 128-bit `int_sum` leave 64 bits (`Issue.sumWraps`)? Polars
    wraps (polars-sum-int)."""
    return (total < I64_MIN) | (total > I64_MAX)


def avg_int_declared(values: pl.Expr) -> pl.Expr:
    """`AVG` of integers in the declared integer type (`AggFn.iavg`): the
    exact mean truncated toward zero; Polars's `mean` is a `Float64`
    (polars-avg-int). The sum is exact on 128 bits, and the mean of 64-bit
    values fits 64 bits. NULL for no values."""
    total = values.cast(pl.Int128).sum()
    n = values.count().cast(pl.Int128)
    q = int_div_trunc(total, pl.when(n == 0).then(1).otherwise(n))
    return pl.when(n == 0).then(None).otherwise(q).cast(pl.Int64)


def float_sum(values: pl.Expr) -> pl.Expr:
    """`SUM` of doubles: Polars's own order (pairwise or Kahan,
    polars-sum-float), within the plan's bound of the reference's correctly
    rounded sum (D25); NULL for no values and one zero."""
    return one_zero(sum_empty_null(values.sum(), values))


def float_avg(values: pl.Expr) -> pl.Expr:
    """`AVG` of doubles: Polars's `mean` (polars-mean-float), NULL for no
    values natively; one zero."""
    return one_zero(values.mean())


def sum_makes_nan(values: pl.Expr) -> pl.Expr:
    """Do the values hold both `+∞` and `-∞`, whose sum Polars makes NaN
    (`nan_creation`, polars-nonfinite-aggregates)? The reference raises."""
    return (values == float("inf")).any() & (values == float("-inf")).any()


def agg_makes_infinite(result: pl.Expr, values: pl.Expr) -> pl.Expr:
    """Do finite values give a `±∞` `SUM` or `AVG` (`Measure.makesInf`,
    #575)?"""
    return values.is_finite().all() & result.is_infinite()


def min_ignore_nan(minimum: pl.Expr) -> pl.Expr:
    """`MIN` of doubles from Polars's `min`, which skips NaN unless every
    value is NaN (polars-min-max-nan): that agrees with NaN as the greatest
    double (`nan_order = GREATEST`). `f64::min` may keep either zero
    (polars-min-max-zero), so the result is read with one zero
    (`Polars.min_ignore_nan`)."""
    return one_zero(minimum)


def nan_through(var: pl.Expr, has_nan: pl.Expr) -> pl.Expr:
    """A variance or deviation from Polars's `var`/`std` and whether the
    group holds a NaN: NaN if it does, as `varOf` gives, wherever `var` is not
    NULL (no values, or a sample of one). Polars's streaming `group_by` over a
    one-row frame gives 0.0 for a NaN (polars-var-pop-one-nan); the guard is
    `Stat.nanGuard`, sound by `Stat.nanGuard_varStat`, as DuckDB's SQL
    (`Dialect.nan_through`)."""
    return pl.when(has_nan & var.is_not_null()).then(pl.lit(float("nan"))).otherwise(var)


def max_nan_greatest(maximum: pl.Expr, has_nan: pl.Expr) -> pl.Expr:
    """`MAX` of doubles from Polars's `max` and whether the group holds a NaN:
    NaN if it does, as NaN is the greatest double (`nan_order = GREATEST`),
    where Polars's `max` skips it (polars-min-max-nan); otherwise the `max`,
    read with one zero (polars-min-max-zero, `Polars.max_nan_greatest`). NULL
    without values, as Polars gives."""
    return pl.when(has_nan).then(pl.lit(float("nan"))).otherwise(one_zero(maximum))

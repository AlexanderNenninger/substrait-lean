"""The generated lowering to Polars, as `pl.Expr` (#271).

For each function Polars does not compute as the reference does, the Lean
build generates a template and proves it gives the reference's outcome under
Polars's profile (`engines/polars/Sverify/Polars/Lowering.lean`,
`Lowering.polars_exact`): `round` and `ceil` without IEEE's `-0.0` for a
negative value that rounds to zero, and the truncating `//` and `%` from
Polars's floored ones. `substrait-check --lowering-table` exports them under
its `"polars"` key, and this module writes one as a Polars expression: its
fields are the arguments' expressions, its calls Polars's own operators, its
conditions `pl.when`, as `sverify.sql.lowering` writes DuckDB's as SQL. The
translation (`sverify_polars.engine`) asks it for those functions, and
`engines/polars/tests/test_lowering_agrees.py` checks its values against the
reference's.

Each call is written as `Profile.polars` states Polars computes it: `//` and
`%` floor, `round` rounds halves away from zero (the `rounding` shim's
argument, as `shims.round_half_away` writes it), the 128-bit `dadd` and
`dsub` are exact on 64-bit operands, and `&`, `+`, `-`, `*` and `**` of
integers are Int64's, exact where the reference's do not raise. Native expressions only, no Python
per row.

A template's `raise` is no Polars expression: `render` gives the rows that
reach it, the conditions of the `CASE`s around it, to its `raise_` hook, which
the translation turns into an issue flag (as `sverify.sql.lowering`'s `raise_`
writes an `error(...)`), and the value there is `NULL`. Polars computes every
branch of a `pl.when` on every row, so a template never calls a function that
fails the query on a row its branch does not take: `>>` gives `**` an exponent
in `0`–`62` only (`Polars.shrPow`, polars-int-pow-exponent), whatever
the other argument.

This interpreter is trusted, as the SQL one is: keep it small.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from typing import Any, Literal

import polars as pl

from sverify._checker import decode_double

Json = Any


def _wide(e: pl.Expr) -> pl.Expr:
    return e.cast(pl.Int128)


#: Polars's operators for the model's functions a template calls.
_BINARY: dict[str, Callable[[pl.Expr, pl.Expr], pl.Expr]] = {
    "lt": lambda a, b: a < b,
    "eq": lambda a, b: a == b,
    "and": lambda a, b: a & b,
    "or": lambda a, b: a | b,
    "idiv": lambda a, b: a // b,
    "imod": lambda a, b: a % b,
    "dmod": lambda a, b: a % b,
    "dadd": lambda a, b: _wide(a) + _wide(b),
    "dsub": lambda a, b: _wide(a) - _wide(b),
    # Int64's `+`, `-`, `*`, which wrap past 64 bits (polars-int-arith): the
    # profile raises there, and the templates call them only inside 64 bits.
    "add": lambda a, b: a + b,
    "sub": lambda a, b: a - b,
    "Substrait.BinFn.mul": lambda a, b: a * b,
    "bit:bitwise_and": lambda a, b: a & b,
    "Substrait.BinFn.ipow": lambda a, b: a.pow(b),
    # `sverify_split_first` (ruling 286): the first part of a split on the literal `t`
    # (polars-split-first).
    "Substrait.BinFn.splitFirst": lambda a, b: a.str.split(b).list.first(),
}
_UNARY: dict[str, Callable[[pl.Expr], pl.Expr]] = {
    "not": lambda a: ~a,
    "isNull": lambda a: a.is_null(),
    # In Polars, as in SQL, a value of a column of numbers that is not NULL is one.
    "isNum": lambda a: a.is_not_null(),
    "Substrait.UnFn.fround": lambda a: a.round(0, mode=_asked_mode("Substrait.UnFn.fround")),
    "Substrait.UnFn.fceil": lambda a: a.ceil(),
    "Substrait.UnFn.length": lambda a: a.str.len_chars().cast(pl.Int64),
}


#: A `mode` of Polars's `round`.
RoundMode = Literal["half_away_from_zero", "half_to_even", "to_zero"]

#: Polars's `round` mode for each rounding behaviour an entry may ask for.
_ROUND_MODES: dict[str, RoundMode] = {
    "TIE_AWAY_FROM_ZERO": "half_away_from_zero",
    "TIE_TO_EVEN": "half_to_even",
}


def _asked_mode(fn: str) -> RoundMode:
    """The `mode=` of Polars's `round` that `fn`'s rendering asks for, as the
    table states it once (`Polars.asks`, ruling 282's C8)."""
    from sverify.sql import lowering as table_export

    return _ROUND_MODES[table_export.asks("polars")[(fn, "rounding")]]


#: A row condition, and Polars's for "every row".
Rows = pl.Expr | None


def _both(a: Rows, b: pl.Expr) -> pl.Expr:
    return b if a is None else a & b


def render(
    fn: str, args: Sequence[pl.Expr], raise_: Callable[[str, pl.Expr], None] | None = None
) -> pl.Expr | None:
    """`fn` of the arguments' expressions as its template writes it, or None
    where Polars's own function is the reference's (no template). `raise_`
    takes each `raise` of the template, its message and the rows that reach
    it."""
    # Imported here: `sverify.sql` loads the engines, this one among them.
    from sverify.sql import lowering as table_export

    tmpl = table_export.table("polars").get(fn)
    if tmpl is None:
        return None

    def go(t: Json, rows: Rows) -> pl.Expr:
        if "field" in t:
            return args[t["field"]]
        if "null" in t:
            return pl.lit(None)
        if "bool" in t:
            return pl.lit(t["bool"], pl.Boolean)
        if "int" in t:
            i = int(t["int"])
            return pl.lit(i, pl.Int64 if -(2**63) <= i < 2**63 else pl.Int128)
        if "code" in t:
            return pl.lit(decode_double(int(t["code"])), pl.Float64)
        if "if" in t:
            c = go(t["if"], rows)
            # `pl.when` takes the `else` branch where the condition is NULL.
            held = c.fill_null(False)
            return (
                pl.when(c)
                .then(go(t["then"], _both(rows, held)))
                .otherwise(go(t["else"], _both(rows, ~held)))
            )
        name, xs = t["fn"], [go(a, rows) for a in t["args"]]
        if name == "raise":
            if raise_ is None:
                raise ValueError(f"lowering table: {fn} raises, and nothing takes its rows")
            raise_(t["message"], _both(rows, pl.lit(True)))
            return pl.lit(None)
        if len(xs) == 1 and name in _UNARY:
            return _UNARY[name](xs[0])
        if len(xs) == 2 and name in _BINARY:
            return _BINARY[name](*xs)
        raise ValueError(f"lowering table: no Polars expression for {name}")

    return go(tmpl, None)

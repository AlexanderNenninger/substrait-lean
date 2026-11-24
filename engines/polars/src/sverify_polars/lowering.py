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
`dsub` are exact on 64-bit operands. Native expressions only, no Python per row.

This interpreter is trusted, as the SQL one is: keep it small.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from typing import Any

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
    "dadd": lambda a, b: _wide(a) + _wide(b),
    "dsub": lambda a, b: _wide(a) - _wide(b),
}
_UNARY: dict[str, Callable[[pl.Expr], pl.Expr]] = {
    "not": lambda a: ~a,
    "isNull": lambda a: a.is_null(),
    "Substrait.UnFn.fround": lambda a: a.round(0, mode=_asked_mode("Substrait.UnFn.fround")),
    "Substrait.UnFn.fceil": lambda a: a.ceil(),
}


#: Polars's `round` mode for each rounding behaviour an entry may ask for.
_ROUND_MODES = {"TIE_AWAY_FROM_ZERO": "half_away_from_zero", "TIE_TO_EVEN": "half_to_even"}


def _asked_mode(fn: str) -> str:
    """The `mode=` of Polars's `round` that `fn`'s rendering asks for, as the
    table states it once (`Polars.asks`, ruling 282's C8)."""
    from sverify.sql import lowering as table_export

    return _ROUND_MODES[table_export.asks("polars")[(fn, "rounding")]]


def render(fn: str, args: Sequence[pl.Expr]) -> pl.Expr | None:
    """`fn` of the arguments' expressions as its template writes it, or None
    where Polars's own function is the reference's (no template)."""
    # Imported here: `sverify.sql` loads the engines, this one among them.
    from sverify.sql import lowering as table_export

    tmpl = table_export.table("polars").get(fn)
    if tmpl is None:
        return None

    def go(t: Json) -> pl.Expr:
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
            return pl.when(go(t["if"])).then(go(t["then"])).otherwise(go(t["else"]))
        name, xs = t["fn"], [go(a) for a in t["args"]]
        if len(xs) == 1 and name in _UNARY:
            return _UNARY[name](xs[0])
        if len(xs) == 2 and name in _BINARY:
            return _BINARY[name](*xs)
        raise ValueError(f"lowering table: no Polars expression for {name}")

    return go(tmpl)

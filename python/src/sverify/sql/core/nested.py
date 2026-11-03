"""Lists and structs (#94): elements, lengths and order (`Expr.listElem`, …).

The list functions of `mkCall`, their SQL and their kinds. A new one goes here,
its `Dialect` hook in the lists section of `_base.Dialect`.
"""

from __future__ import annotations

from collections.abc import Callable

from sverify.sql.core._base import Bin, Expr, FixedKind, Kind, Un, _Writer, expr_kind, register


def call(name: str, args: list[Expr]) -> Expr | None:
    """`mkCall`'s nested functions."""
    match name, args:
        case "list_lt", [a, b]:
            return Bin("list_lt", a, b)
        case "cardinality", [a]:
            return Un("cardinality", a)
    return None


def expr(
    self: _Writer, e: Expr, ref: Callable[[int], str], cols: list[Kind | None], ctx: Kind | None
) -> str | None:
    """`_Writer.expr` of the nested operations."""
    d = self.d

    def go(x: Expr, k: Kind | None = None) -> str:
        return self.expr(x, ref, cols, k)

    def kind(x: Expr) -> Kind | None:
        return expr_kind(x, cols)

    match e:
        case Bin(op="list_lt", left=a, right=b):
            return d.list_lt(go(a, None), go(b, None))
        case Un(op="list_elem", arg=a, digits=offset):
            return d.list_element(go(a, kind(a)), offset)
        case Un(op="cardinality", arg=a):
            return d.cardinality(go(a, kind(a)))
    return None


#: The result kinds of this area's `Un` and `Bin` operations (`Expr.kind`).
UN_KINDS: dict[str, FixedKind] = {"cardinality": "int"}
BIN_KINDS: dict[str, FixedKind] = {}

register(call, expr, un_kinds=UN_KINDS, bin_kinds=BIN_KINDS)

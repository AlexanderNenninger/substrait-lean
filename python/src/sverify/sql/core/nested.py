"""Lists and structs (#94): elements, lengths and order (`Expr.listElem`, …).

The list functions of `mkCall`, their SQL and their kinds. A new one goes here,
its `Dialect` hook in the lists section of `_base.Dialect`.
"""

from __future__ import annotations

from collections.abc import Callable

from sverify.sql.core._base import (
    Bin,
    Expr,
    FixedKind,
    Kind,
    Lst,
    Un,
    _Writer,
    expr_kind,
    register,
)


def call(name: str, args: list[Expr]) -> Expr | None:
    """`mkCall`'s nested functions."""
    match name, args:
        case "list_lt", [a, b]:
            return Bin("list_lt", a, b)
        case "cardinality", [a]:
            return Un("cardinality", a)
        case "flatten", [a]:
            return Un("flatten", a)
        case ("list_prepend" | "list_concat" | "list_contains" | "list_position") as op, [a, b]:
            return Bin(op, a, b)
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
        case Un(op="flatten", arg=a):
            return d.list_fn("flatten", [go(a, kind(a))])
        case Bin(op="list_prepend", left=x, right=lst):
            k = expr_kind(e, cols)
            return d.list_fn(
                "list_prepend", [go(x, k.elem if isinstance(k, Lst) else None), go(lst, k)]
            )
        case Bin(op="list_concat", left=a, right=b):
            k = expr_kind(e, cols)
            return d.list_fn("list_concat", [go(a, k), go(b, k)])
        case Bin(op=("list_contains" | "list_position") as op, left=lst, right=x):
            k = kind(lst)
            elem = k.elem if isinstance(k, Lst) else kind(x)
            return d.list_fn(op, [go(lst, k if isinstance(k, Lst) else Lst(elem)), go(x, elem)])
    return None


#: The result kinds of this area's `Un` and `Bin` operations (`Expr.kind`).
UN_KINDS: dict[str, FixedKind] = {"cardinality": "int"}
BIN_KINDS: dict[str, FixedKind] = {"list_position": "int"}

register(call, expr, un_kinds=UN_KINDS, bin_kinds=BIN_KINDS)

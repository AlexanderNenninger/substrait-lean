"""Black boxes (#325): the functions of `sverify.black_box`'s table, which the
checker treats as opaque (`SubstraitLean/BlackBox.lean`).

`mkCall` reads a call of a scalar black box as `Un`/`Bin` `black_box` with its
name in `param`; its SQL is the dialect's (`Dialect.black_box`), which only
DuckDB has (#271). An aggregate black box is a `Measure` of `fn` `black_box`
(`_base.py`, with the other aggregates).
"""

from __future__ import annotations

from collections.abc import Callable

from sverify import black_box
from sverify.sql.core._base import Bin, Expr, Kind, Lit, Un, _Writer, register

#: The kind of each `black_box.Ty`; `any` takes the argument's own.
KINDS: dict[str, Kind] = {
    "int": "int", "double": "float", "str": "str", "bool": "bool", "date": "date",
}  # fmt: skip


def call(name: str, args: list[Expr]) -> Expr | None:
    """`mkCall`'s black boxes: `Parse.lean`'s, one or two arguments."""
    if name not in black_box.SCALARS:
        return None
    match args:
        case [a]:
            return Un("black_box", a, param=name)
        case [a, b]:
            return Bin("black_box", a, b, param=name)
    return None


def result_kind(name: str) -> Kind | None:
    """The result kind of the black box `name` (`Parse.bbScalarKind`)."""
    row = black_box.SCALARS.get(name) or black_box.AGGREGATES.get(name)
    return KINDS.get(row.result) if row is not None else None


def expr(
    self: _Writer, e: Expr, ref: Callable[[int], str], cols: list[Kind | None], ctx: Kind | None
) -> str | None:
    """`_Writer.expr` of the black boxes: the dialect's SQL of the row. An
    `atom` or `any` argument is written with its own kind."""
    match e:
        case Un(op="black_box", arg=a, param=name):
            args = [a]
        case Bin(op="black_box", left=a, right=b, param=name):
            args = [a, b]
        case _:
            return None
    row = black_box.SCALARS[name]
    sqls = [
        self.expr(x, ref, cols, None)
        if ty not in KINDS
        # A constant date is an integer, its days.
        else self.d.date_lit(x.value)
        if ty == "date" and isinstance(x, Lit) and isinstance(x.value, int)
        else self.operand(x, KINDS[ty], ref, cols, name)
        for x, ty in zip(args, row.args, strict=True)
    ]
    sql = self.d.black_box(row, sqls)
    return self.d.canon(sql) if row.result == "double" else sql


register(call, expr, un_kinds={}, bin_kinds={})

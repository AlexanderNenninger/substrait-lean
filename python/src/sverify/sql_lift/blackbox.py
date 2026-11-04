"""The lift's black boxes (#325): DuckDB functions the checker treats as
opaque, from the table of `sverify.black_box` (`SubstraitLean/BlackBox.lean`).

A call of a black box lifts to a call of the extension function of its name,
under sverify's URN (`black_box.URN`), with its row's argument and result
types. SQLGlot reads most of them as `Anonymous`; `_rewrite` gives each call
a node of its own (`BlackBoxCall`, `BlackBoxAgg`) before the lift checks the
query's functions, so that an aggregate is found as one (`AGG_RULES`).

A row's arguments are its SQL's (`BlackBox.duckdb`): `base64(encode(s))`
takes the string `s`, DuckDB's `base64` a BLOB.
"""

from __future__ import annotations

from typing import Any

import ibis.expr.datatypes as dt
import sqlglot.expressions as sge

from sverify import black_box
from sverify.plan_json import Unsupported
from sverify.sql_lift._base import (
    _AGGREGATES,
    _KNOWN,
    AGG_RULES,
    PARSE_REWRITES,
    Column,
    E,
    Sub,
    _fn,
    _Lift,
    register,
)


class BlackBoxCall(sge.Anonymous):
    """A call of a scalar black box (`this` its name)."""


class BlackBoxAgg(sge.Expression, sge.AggFunc):
    """A call of an aggregate black box: `this` its argument, `fname` its name
    (a string literal)."""

    arg_types = {"this": True, "fname": True}


#: The type of each `black_box.Ty`.
_TYPES: dict[str, Any] = {"int": dt.int64, "double": dt.float64, "str": dt.string,
                          "bool": dt.boolean}  # fmt: skip


def _accepts(ty: str, t: Any) -> bool:
    return (
        t.is_null()
        or ty == "any"
        or (ty == "int" and t.is_integer())
        or (ty == "double" and t.is_floating())
        or (ty == "str" and t.is_string())
        or (ty == "bool" and t.is_boolean())
    )


def _unwrap(name: str, arg: sge.Expression) -> sge.Expression:
    """The SQL argument of a row whose SQL wraps it: `encode(s)` of `base64`'s."""
    if "encode({0})" in black_box.SCALARS[name].duckdb:
        if not isinstance(arg, sge.Encode):
            raise Unsupported(
                f"{name} of a BLOB is not supported: write {name}(encode(s)) of a string s"
            )
        return arg.this
    return arg


def _rewrite(tree: sge.Expr) -> sge.Expr:
    """Each black box's call as its own node."""

    def node(n: sge.Expr) -> sge.Expr:
        if isinstance(n, sge.ToBase64):
            # SQLGlot's `to_base64(x)`, DuckDB's other name for `base64`.
            return BlackBoxCall(this="base64", expressions=[n.this])
        if type(n) is not sge.Anonymous:
            return n
        name = n.name.lower()
        if name in black_box.SCALARS:
            return BlackBoxCall(this=name, expressions=list(n.expressions))
        if name in black_box.AGGREGATES:
            if len(n.expressions) != 1:
                raise Unsupported(f"{name} takes one argument")
            return BlackBoxAgg(this=n.expressions[0], fname=sge.Literal.string(name))
        return n

    return tree.transform(node, copy=False)


def _scalar(lf: _Lift, node: BlackBoxCall, sub: Sub, scope: list[Column]) -> E:
    row = black_box.SCALARS[node.name]
    args = list(node.expressions)
    if len(args) != len(row.args):
        raise Unsupported(f"{row.name} takes {len(row.args)} argument(s)")
    js = []
    for a, ty in zip(args, row.args, strict=True):
        e = sub(_unwrap(row.name, a))
        if not _accepts(ty, e.type):
            raise Unsupported(f"{row.name} of a {e.type} is not supported")
        js.append(lf.to(e, _TYPES[ty]).json if ty != "any" else e.json)
    out = _TYPES[row.result]
    return E(_fn(row.name, js, out), out)


def _aggregate(lf: _Lift, node: sge.Expression, a: E) -> tuple[str, Any]:
    name = node.args["fname"].this
    row = black_box.AGGREGATES[name]
    if not _accepts(row.args[0], a.type):
        raise Unsupported(f"{name} of a {a.type} is not supported")
    return name, _TYPES[row.result]


_KNOWN.update(black_box.NAMES)
PARSE_REWRITES.append(_rewrite)
_AGGREGATES[BlackBoxAgg] = "black_box"
AGG_RULES[BlackBoxAgg] = _aggregate

register({BlackBoxCall: _scalar})

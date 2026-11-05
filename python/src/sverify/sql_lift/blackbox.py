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
                          "bool": dt.boolean, "date": dt.date, "timestamp": dt.timestamp(scale=6),
                          "doubles": dt.Array(value_type=dt.float64),
                          "ints": dt.Array(value_type=dt.int64),
                          "strs": dt.Array(value_type=dt.string)}  # fmt: skip

#: The types an argument is converted to (`lf.to`); the others are taken as
#: they are.
_CONVERTED = ("int", "double", "str", "bool", "date")

#: DuckDB's other names of black boxes: its vector functions of fixed-size
#: ARRAYs, which the model reads as lists, are those of lists (#327).
ALIASES = {
    "array_cosine_similarity": "list_cosine_similarity",
    "array_cosine_distance": "list_cosine_distance",
    "array_distance": "list_distance",
    "list_dot_product": "list_inner_product",
    "array_inner_product": "list_inner_product",
    "array_dot_product": "list_inner_product",
    "array_negative_inner_product": "list_negative_inner_product",
    "array_negative_dot_product": "list_negative_inner_product",
    "list_negative_dot_product": "list_negative_inner_product",
    "fsum": "kahan_sum",
    "sumkahan": "kahan_sum",
}

#: DuckDB functions near the black boxes that the model cannot hold yet.
REFUSED = {
    "histogram": "histogram's result is a MAP, which the model lacks (#326)",
    "histogram_exact": "histogram_exact's result is a MAP, which the model lacks (#326)",
    "weighted_avg": "weighted_avg takes two arguments; black-box aggregates take one (#326)",
    "wavg": "wavg takes two arguments; black-box aggregates take one (#326)",
}


def _accepts(ty: str, t: Any) -> bool:
    return (
        t.is_null()
        or ty == "any"
        or (ty == "int" and t.is_integer())
        or (ty == "double" and t.is_floating())
        or (ty == "str" and t.is_string())
        or (ty == "bool" and t.is_boolean())
        or (ty == "date" and t.is_date())
        or (ty == "atom" and (t.is_integer() or t.is_string() or t.is_boolean()))
        or (ty == "doubles" and t.is_array() and t.value_type.is_float64())
        or (ty == "ints" and t.is_array() and t.value_type.is_integer())
        or (ty == "strs" and t.is_array() and t.value_type.is_string())
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
        if isinstance(n, (sge.CosineDistance, sge.EuclideanDistance)):
            # SQLGlot's `list_cosine_distance(a, b)` and `list_distance(a, b)`.
            name = "list_cosine_distance" if isinstance(n, sge.CosineDistance) else "list_distance"
            return BlackBoxCall(this=name, expressions=[n.this, n.expression])
        if isinstance(n, (sge.Kurtosis, sge.Skewness)):
            # SQLGlot's `kurtosis(x)` and `skewness(x)`.
            name = "kurtosis" if isinstance(n, sge.Kurtosis) else "skewness"
            return BlackBoxAgg(this=n.this, fname=sge.Literal.string(name))
        if isinstance(n, sge.Split):
            # SQLGlot's `string_split(s, sep)` (also `str_split`, `string_to_array`).
            return BlackBoxCall(this="string_split", expressions=[n.this, n.expression])
        if isinstance(n, sge.Format):
            # SQLGlot's `format(fmt, …)`.
            return BlackBoxCall(this="format", expressions=[n.this, *n.expressions])
        if type(n) is not sge.Anonymous:
            return n
        name = n.name.lower()
        if name in REFUSED:
            raise Unsupported(REFUSED[name])
        name = ALIASES.get(name, name)
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
        if row.name == "bit_count" and not e.type.is_int64():
            # DuckDB counts the bits of the argument's own width.
            raise Unsupported(f"bit_count of a {e.type}: cast it to BIGINT (#326)")
        js.append(lf.to(e, _TYPES[ty]).json if ty in _CONVERTED else e.json)
    out = _TYPES[row.result]
    return E(_fn(row.name, js, out), out)


def _aggregate(lf: _Lift, node: sge.Expression, a: E) -> tuple[str, Any]:
    name = node.args["fname"].this
    row = black_box.AGGREGATES[name]
    # An integer becomes a double (`Parse.lean`), as DuckDB converts it.
    if not (_accepts(row.args[0], a.type) or (row.args[0] == "double" and a.type.is_integer())):
        raise Unsupported(f"{name} of a {a.type} is not supported")
    return name, _TYPES[row.result]


_KNOWN.update(black_box.NAMES, ALIASES, REFUSED)
PARSE_REWRITES.append(_rewrite)
_AGGREGATES[BlackBoxAgg] = "black_box"
AGG_RULES[BlackBoxAgg] = _aggregate

register({BlackBoxCall: _scalar})

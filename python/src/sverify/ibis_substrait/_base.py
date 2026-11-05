"""Shared parts of the Ibis producer: the expression and relation
translators, the dispatch tables the area modules register their rules
into, exact decimal types, and the entry points.

Part of the Ibis producer (`sverify.ibis_substrait`), derived from
ibis-substrait (Apache License 2.0); `__init__.py` notes the changes.
"""

from __future__ import annotations

import functools
import json
import math
from collections.abc import Callable, Iterable, Mapping
from decimal import Decimal
from typing import Any

import ibis.expr.datatypes as dt
import ibis.expr.operations as ops
import ibis.expr.types as ir

from sverify import _functions
from sverify.plan_json import (
    Json,
    Unsupported,
    call,
    cast_json,
    compiling,
    decimal_literal,
    decimal_type_of,
    field_ref,
    literal,
    plan,
    same_type,
)
from sverify.plan_json import decimal_dtype as _decimal

# --------------------------------------------------------------------------
# Expressions


#: Where each relation's columns start in the input of the expression being
#: translated: the input itself at 0, join tables at their join offsets.
Offsets = Mapping[Any, int]


class Exprs:
    """Translates value expressions over one input."""

    def __init__(self, offsets: Offsets, windows: Mapping[Any, int] | None = None):
        self.offsets = offsets
        # Window functions computed beforehand, by column (see `project`).
        self.windows = windows or {}

    def __call__(self, op: Any, to: Any = None) -> Json:
        """`op`, cast to `to` when its type differs. A decimal `to` gives
        the scale: a decimal or integer is brought to it exactly (#27)."""
        if to is not None and to.is_decimal() and not op.dtype.is_null():
            return self.rescaled(op, to)
        e = self.translate(op)
        if to is not None and not op.dtype.is_null() and not same_type(exact(op), to):
            return cast_json(e, to)
        return e

    def operand(self, op: Any) -> Json:
        """An argument of decimal arithmetic or a comparison, which the model
        computes at a common scale itself: a float constant as its decimal."""
        if _float_const(op):
            return literal(_const_decimal(op), dt.Decimal(precision=None, scale=None))
        return self(op)

    def rescaled(self, op: Any, to: Any) -> Json:
        """`op` at the scale of the decimal `to`: a cast to that scale with
        the integer digits it has, or a constant at that scale."""
        t, s = exact(op), to.scale
        v = op.value if isinstance(op, ops.Literal) else None
        if _float_const(op) or (isinstance(v, int | Decimal) and not isinstance(v, bool)):
            d = _const_decimal(op) if _float_const(op) else Decimal(op.value)
            if d == d.quantize(Decimal(1).scaleb(-s)):
                digits = len(str(abs(int(d.scaleb(s)))))
                return decimal_literal(d, _decimal(max(digits, s, 1), s))
        e = self.translate(op)
        if t.is_decimal() or t.is_integer():
            p, s0 = _digits(t, op)
            return e if s0 == s else cast_json(e, _decimal(p - s0 + s, s))
        return cast_json(e, to)

    def translate(self, op: Any) -> Json:
        if op in self.windows:
            return field_ref(self.windows[op])
        rule = _RULES.get(type(op))
        if rule is None:
            name = type(op).__name__
            reason = _REFUSED.get(name)
            raise Unsupported(
                f"{_OP_LABELS.get(name, name)} is not supported" + (f": {reason}" if reason else "")
            )
        return rule(self, op)


#: What a refusal calls an Ibis operation, where its class name is not what
#: users write (#655).
_OP_LABELS = {"TimestampNow": "ibis.now()", "DateNow": "ibis.today()"}

#: Why some operations are refused (#58).
_REFUSED: dict[str, str] = {}


def register_refusals(reasons: Mapping[str, str]) -> None:
    """Add one area's refusal reasons to `_REFUSED`, by operation name."""
    if dup := _REFUSED.keys() & reasons.keys():
        raise ValueError(f"refusals registered twice: {sorted(dup)}")
    _REFUSED.update(reasons)


#: The rule of each expression operation; each area module registers its own.
_RULES: dict[Any, Callable[[Exprs, Any], Json]] = {}


def register(rules: Mapping[Any, Callable[[Exprs, Any], Json]]) -> None:
    """Add one area's expression rules to `_RULES`; each operation has one rule."""
    if dup := _RULES.keys() & rules.keys():
        raise ValueError(f"rules registered twice: {sorted(t.__name__ for t in dup)}")
    _RULES.update(rules)


def _common(*types: Any) -> Any:
    return dt.highest_precedence([t for t in types if not t.is_null()] or [dt.null])


# --------------------------------------------------------------------------
# Decimals (#27, #67)
#
# Ibis types decimal arithmetic loosely: `decimal(15, 2) * decimal(15, 2)` is a
# `decimal(15, 2)` to Ibis, but its SQL computes the product exactly, at scale
# 4, as the Lean model does. The plan follows the SQL, so the producer works
# out each decimal's exact type here, as `Parse.decimalCall` does: `+` and `-`
# at the larger scale with one more integer digit, `×` at the sum of the
# scales, `SUM` ten more digits, `AVG` four more digits and decimal places,
# all at most 38 digits. A float constant next to a decimal is a decimal, as
# Ibis writes it into SQL (`0.05`); any other double makes a double.


def _float_const(op: Any) -> bool:
    return (
        isinstance(op, ops.Literal)
        and op.dtype.is_floating()
        and isinstance(op.value, float)
        and math.isfinite(op.value)
    )


def _const_decimal(op: Any) -> Decimal:
    """A float constant as the decimal Ibis's SQL writes for it."""
    return Decimal(repr(op.value))


def _digits(t: Any, op: Any) -> tuple[int, int]:
    """`(precision, scale)` of a decimal, an integer (a constant's own digits,
    else a `BIGINT`'s 19) or a float constant (its decimal)."""
    if _float_const(op):
        d = decimal_type_of(_const_decimal(op))
        return d.precision, d.scale
    if t.is_decimal():
        return t.precision, t.scale
    if isinstance(op, ops.Literal) and isinstance(op.value, int):
        return max(1, len(str(abs(op.value)))), 0
    return 19, 0


def _decimal_args(*args: Any) -> bool:
    """Whether `args` compute as decimals: one of them is a decimal, and the
    others are decimals, integers, float constants or NULL."""
    ts = [exact(a) for a in args]
    return any(t.is_decimal() for t in ts) and all(
        t.is_decimal() or t.is_integer() or t.is_null() or _float_const(a)
        for a, t in zip(args, ts, strict=True)
    )


def _common_exact(args: Iterable[Any], t: Any) -> Any:
    """The type `args` are brought to as one value (`CASE`, `COALESCE`): the
    largest scale and the most integer digits, or a double."""
    args = [a for a in args if not a.dtype.is_null()]
    if not _decimal_args(*args):
        return dt.float64 if any(exact(a).is_floating() for a in args) else t
    ds = [_digits(exact(a), a) for a in args]
    s = max(s for _, s in ds)
    return _decimal(max(p - s0 for p, s0 in ds) + s, s)


def _field_exact(rel: Any, name: str) -> Any:
    """The exact type of column `name` of `rel`, from the expression that
    computes it."""
    schema: Any = rel.schema
    for attr in ("values", "groups", "metrics"):
        v = getattr(rel, attr, None)
        if v is not None and name in v:
            return exact(v[name])
    if isinstance(rel, ops.Set):
        sides = [ops.Field(rel.left, name), ops.Field(rel.right, name)]
        return _common_exact(sides, schema[name])
    parent = getattr(rel, "parent", None)
    if isinstance(parent, ops.Relation) and name in parent.schema:
        return exact(ops.Field(parent, name))
    return schema[name]


def exact(op: Any) -> Any:
    """The type of `op`'s value in the plan: Ibis's, except for decimals."""
    return _exact(op)


@functools.cache
def _exact(op: Any) -> Any:
    t = op.dtype
    if not t.is_decimal():
        return t
    match op:
        case ops.Literal(value=v) if v is not None:
            return decimal_type_of(v)
        case ops.Field():
            return _field_exact(op.rel, op.name)
        case ops.ScalarSubquery():
            rel: Any = op.rel
            return _field_exact(rel, rel.schema.names[0])
        case ops.WindowFunction():
            return exact(op.func)
        case ops.Add() | ops.Subtract() | ops.Multiply():
            if not _decimal_args(op.left, op.right):
                return dt.float64
            p1, s1 = _digits(exact(op.left), op.left)
            p2, s2 = _digits(exact(op.right), op.right)
            if isinstance(op, ops.Multiply):
                return _decimal(p1 + p2 + 1, s1 + s2)
            s = max(s1, s2)
            return _decimal(max(p1 - s1, p2 - s2) + s + 1, s)
        case ops.Negate() | ops.Abs() | ops.Min() | ops.Max():
            return exact(op.arg)
        case ops.Sum():
            a = exact(op.arg)
            return _decimal(a.precision + 10, a.scale) if a.is_decimal() else t
        case ops.Mean():
            a = exact(op.arg)
            return _decimal(a.precision + 4, a.scale + 4) if a.is_decimal() else t
        case ops.IfElse():
            return _common_exact([op.true_expr, op.false_null_expr], t)
        case ops.SearchedCase() | ops.SimpleCase():
            return _common_exact([*op.results, op.default], t)
        case ops.Coalesce() | ops.Greatest() | ops.Least():
            return _common_exact(op.arg, t)
        case ops.NullIf():
            return exact(op.arg)
    return t


def _unary(name: str) -> Callable[[Exprs, Any], Json]:
    return lambda x, op: call(name, [x(op.arg)])


#: What the function table's arguments are cast to (`sverify._functions`).
_CASTS = {"str": None, "int": dt.int64, "float": dt.float64}


def table_rules(
    area: str, by_group: Mapping[str, Callable[[str], Callable[[Exprs, Any], Json]]] | None = None
) -> dict[Any, Callable[[Exprs, Any], Json]]:
    """The rules of an area's rows of the function table, by Ibis operation:
    the group's rule (`by_group`, of the function's name), or by default the
    function of the operation's arguments, each cast to the row's kind."""

    def plain(f: _functions.Fn) -> Callable[[Exprs, Any], Json]:
        casts = [_CASTS[k] for k in f.args]
        return lambda x, op: call(f.name, [x(a, t) for a, t in zip(op.args, casts, strict=True)])

    by_group = by_group or {}
    return {
        getattr(ops, n): by_group[f.group](f.name) if f.group in by_group else plain(f)
        for f in _functions.area(area)
        for n in f.ibis
    }


def rel(op: Any) -> Json:
    rule = _RELS.get(type(op))
    if rule is None:
        raise Unsupported(f"{type(op).__name__} is not supported")
    return rule(op)


#: The rule of each relation operation; area modules register theirs.
_RELS: dict[Any, Callable[[Any], Json]] = {}


def register_rels(rules: Mapping[Any, Callable[[Any], Json]]) -> None:
    """Add one area's relation rules to `_RELS`; each operation has one rule."""
    if dup := _RELS.keys() & rules.keys():
        raise ValueError(f"relation rules registered twice: {sorted(t.__name__ for t in dup)}")
    _RELS.update(rules)


def _sort_key(x: Exprs, k: Any) -> Json:
    order = "ASC" if k.ascending else "DESC"
    nulls = "FIRST" if k.nulls_first else "LAST"
    return {"expr": x(k.arg), "direction": f"SORT_DIRECTION_{order}_NULLS_{nulls}"}


# --------------------------------------------------------------------------
# Plans


def to_substrait(expr: ir.Table, semantics: str = "reference") -> Json:
    """The Substrait plan of an Ibis table expression, as protobuf JSON. Under
    `semantics="polars"`, integer `//` and `%` are Polars's: they state
    `division_type` = `FLOOR` (`Profile.polars`)."""
    with compiling(semantics) as compiler:
        op: Any = expr.op()
        return plan(compiler, rel(op), list(op.schema.names))


def to_substrait_json(expr: ir.Table, semantics: str = "reference") -> str:
    return json.dumps(to_substrait(expr, semantics))

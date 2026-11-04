"""Core rules of the Ibis producer: columns, constants, arithmetic,
comparisons, logic, conditionals, NULL handling, math and bitwise operations.

Part of the Ibis producer (`sverify.ibis_substrait`), derived from
ibis-substrait (Apache License 2.0); `__init__.py` notes the changes.
"""

from __future__ import annotations

import math
from collections.abc import Callable
from typing import Any

import ibis.expr.datatypes as dt
import ibis.expr.operations as ops
import ibis.expr.rules as rlz

from sverify.ibis_substrait._base import (
    Exprs,
    _common,
    _common_exact,
    _decimal_args,
    _unary,
    exact,
    register,
    register_refusals,
    same_type,
    table_rules,
)
from sverify.plan_json import (
    Json,
    Unsupported,
    call,
    cast_json,
    field_ref,
    ieee_divide,
    if_then,
    literal,
    type_json,
)

_NONDETERMINISTIC = "each run gives another value, so no contract can be proved about it"


def _field(x: Exprs, op: Any) -> Json:
    if op.rel not in x.offsets:
        raise Unsupported(
            f"column {op.name} refers to a relation outside its input "
            "(correlated subqueries are only supported in EXISTS)"
        )
    return field_ref(x.offsets[op.rel] + op.rel.schema.names.index(op.name))


def _literal(x: Exprs, op: Any) -> Json:
    return literal(op.value, op.dtype)


def _arith(name: str) -> Callable[[Exprs, Any], Json]:
    """Ibis computes in the operation's type: cast the operands to it. The
    model computes decimals at their exact scales itself."""

    def rule(x: Exprs, op: Any) -> Json:
        if exact(op).is_decimal():
            return call(name, [x.operand(op.left), x.operand(op.right)])
        return call(name, [x(op.left, exact(op)), x(op.right, exact(op))])

    return rule


def _modulus(x: Exprs, op: Any) -> Json:
    """`%`; of doubles, sverify's own `sverify_fmod` (C's `fmod`, #256), as
    Substrait's `modulus` has no double impl."""
    if exact(op).is_floating():
        return call("sverify_fmod", [x(op.left, exact(op)), x(op.right, exact(op))])
    return _arith("modulus")(x, op)


def _compare(name: str) -> Callable[[Exprs, Any], Json]:
    def rule(x: Exprs, op: Any) -> Json:
        if _decimal_args(op.left, op.right):
            return call(name, [x.operand(op.left), x.operand(op.right)])
        t = _common(exact(op.left), exact(op.right))
        return call(name, [x(op.left, t), x(op.right, t)])

    return rule


def _power(x: Exprs, op: Any) -> Json:
    # Ibis types integer powers as doubles, but its SQL computes `POW` in
    # integers (which fails on overflow and negative exponents) and converts
    # the result.
    if op.left.dtype.is_integer() and op.right.dtype.is_integer():
        t = _common(op.left.dtype, op.right.dtype)
        return cast_json(call("power", [x(op.left, t), x(op.right, t)]), op.dtype)
    return call("power", [x(op.left, op.dtype), x(op.right, op.dtype)])


def _divide(x: Exprs, op: Any) -> Json:
    # Ibis's `/` is division of doubles (upstream divided integers).
    return call("divide", [x(op.left, dt.float64), x(op.right, dt.float64)])


def _floor_divide(x: Exprs, op: Any) -> Json:
    if op.left.dtype.is_integer() and op.right.dtype.is_integer():
        # Floor division in integers, as `sverify.engine` compiles `//`. With
        # the signs apart, it is `(a + 1) / b - 1` for `a < 0 < b`, and
        # `(a - 1) / b - 1` for `b < 0 < a`: no step can overflow, which the
        # range analysis sees from the branch's condition (#202). Otherwise
        # the truncating quotient is the floor.
        t = op.dtype
        a, b = x(op.left, t), x(op.right, t)
        zero, one = literal(0, t), literal(1, t)

        def lt(u: Json, v: Json) -> Json:
            return call("lt", [u, v])

        def floor_apart(shift: str) -> Json:
            q = call("divide", [call(shift, [a, one]), b])
            return call("subtract", [q, one])

        return if_then(
            [
                (call("and", [lt(a, zero), lt(zero, b)]), floor_apart("add")),
                (call("and", [lt(zero, a), lt(b, zero)]), floor_apart("subtract")),
            ],
            call("divide", [a, b]),
        )
    q = call("divide", [x(op.left, dt.float64), x(op.right, dt.float64)])
    return cast_json(call("floor", [q]), op.dtype)


def _rounding(name: str) -> Callable[[Exprs, Any], Json]:
    # `CAST(FLOOR(x) AS <type>)` and friends, as Ibis's base compiler writes them.
    def rule(x: Exprs, op: Any) -> Json:
        args = [x(op.arg)]
        if getattr(op, "digits", None) is not None:
            args.append(x(op.digits))
        e = call(name, args)
        return e if same_type(op.arg.dtype, op.dtype) else cast_json(e, op.dtype)

    return rule


def _variadic(name: str) -> Callable[[Exprs, Any], Json]:
    return lambda x, op: call(name, [x(a, exact(op)) for a in op.arg])


def _clip(x: Exprs, op: Any) -> Json:
    arg = x(op.arg, op.dtype)
    if op.upper is not None:
        arg = if_then([(call("is_null", [arg]), arg)], call("least", [x(op.upper, op.dtype), arg]))
    if op.lower is not None:
        arg = if_then(
            [(call("is_null", [arg]), arg)], call("greatest", [x(op.lower, op.dtype), arg])
        )
    return arg


def _between(x: Exprs, op: Any) -> Json:
    if _decimal_args(op.arg, op.lower_bound, op.upper_bound):
        a, lo, hi = x.operand(op.arg), x.operand(op.lower_bound), x.operand(op.upper_bound)
    else:
        t = _common(exact(op.arg), exact(op.lower_bound), exact(op.upper_bound))
        a, lo, hi = x(op.arg, t), x(op.lower_bound, t), x(op.upper_bound, t)
    return call("and", [call("gte", [a, lo]), call("lte", [a, hi])])


def _in_values(x: Exprs, op: Any) -> Json:
    args = [op.value, *op.options]
    t = _common_exact(args, _common(*(exact(a) for a in args)))
    return {"singularOrList": {"value": x(op.value, t), "options": [x(o, t) for o in op.options]}}


def _if_else(x: Exprs, op: Any) -> Json:
    t = exact(op)
    return if_then([(x(op.bool_expr), x(op.true_expr, t))], x(op.false_null_expr, t))


def _searched_case(x: Exprs, op: Any) -> Json:
    t = exact(op)
    ifs = [(x(c), x(r, t)) for c, r in zip(op.cases, op.results, strict=True)]
    return if_then(ifs, x(op.default, t))


def _simple_case(x: Exprs, op: Any) -> Json:
    args = [op.base, *op.cases]
    t = _common_exact(args, _common(*(exact(a) for a in args)))
    r_t = exact(op)
    ifs = [
        (call("equal", [x(op.base, t), x(c, t)]), x(r, r_t))
        for c, r in zip(op.cases, op.results, strict=True)
    ]
    return if_then(ifs, x(op.default, r_t))


def _is_nan(x: Exprs, op: Any) -> Json:
    # FALSE for NULL, as Ibis's DataFusion SQL writes it.
    arg = x(op.arg)
    return call("and", [call("is_not_null", [arg]), call("is_nan", [arg])])


def _double(v: float) -> Json:
    return literal(v, dt.float64)


def _log(x: Exprs, op: Any) -> Json:
    # Ibis's SQL: `LN(x)`, `LOG2(x)` or `LOG10(x)` for a constant base 2 or
    # 10, and `LN(x) / LN(b)` otherwise, which is Substrait's `logb(x, b)`.
    arg = x(op.arg, dt.float64)
    if op.base is None:
        return call("ln", [arg])
    if isinstance(op.base, ops.Literal) and op.base.value in (2, 10):
        return call(f"log{op.base.value}", [arg])
    return call("logb", [arg, x(op.base, dt.float64)])


def _sign(x: Exprs, op: Any) -> Json:
    # -1, 0 or 1 in the argument's type; NaN for NaN, which is tested first
    # (NaN is above every number).
    arg, t = x(op.arg), op.arg.dtype
    ifs = [
        (call("lt", [arg, literal(0, t)]), literal(-1, t)),
        (call("gt", [arg, literal(0, t)]), literal(1, t)),
    ]
    if t.is_floating():
        ifs.insert(0, (call("is_nan", [arg]), arg))
    return if_then(ifs, arg)


def _is_inf(x: Exprs, op: Any) -> Json:
    # Ibis's SQL: `NOT isnan(x) AND abs(x) = inf`, which is this.
    arg = x(op.arg, dt.float64)
    inf = [call("equal", [arg, _double(s * math.inf)]) for s in (1, -1)]
    return call("or", inf)


def _bitwise(name: str) -> Callable[[Exprs, Any], Json]:
    def rule(x: Exprs, op: Any) -> Json:
        if "shift" in name and not op.dtype.is_int64():
            # Narrower shifts lose bits at their own width.
            raise Unsupported(f"shifts of {op.dtype} are not supported; cast to int64")
        return call(name, [x(op.left, op.dtype), x(op.right, op.dtype)])

    return rule


class DecimalDiv(ops.Value):
    """`left / right`, a decimal by an integer, at the scale of the decimal
    type `to`, rounded half away from zero (`sverify_decimal_div`). Ibis has
    no such operation: `sverify._linear` finishes a decimal `AVG` with it
    from the group's sum and count, as the model computes the `AVG`
    (`Parse.decimalAvgs`)."""

    left: ops.Value
    right: ops.Value
    to: dt.DataType

    shape = rlz.shape_like("left")

    @property
    def dtype(self) -> Any:
        return self.to


def _decimal_div(x: Exprs, op: Any) -> Json:
    j = call("sverify_decimal_div", [x(op.left), x(op.right)])
    j["scalarFunction"]["outputType"] = type_json(op.to)
    return j


def _xor(x: Exprs, op: Any) -> Json:
    # Ibis's DataFusion SQL: `(a AND NOT b) OR (NOT a AND b)`.
    a, b = x(op.left), x(op.right)
    return call("or", [call("and", [a, call("not", [b])]), call("and", [call("not", [a]), b])])


register(
    {
        ops.Field: _field,
        ops.Literal: _literal,
        ops.Add: _arith("add"),
        ops.Subtract: _arith("subtract"),
        ops.Multiply: _arith("multiply"),
        ops.Modulus: _modulus,
        ops.Power: _power,
        ops.Divide: _divide,
        ops.FloorDivide: _floor_divide,
        ops.Negate: _unary("negate"),
        ops.Abs: _unary("abs"),
        ops.Ceil: _rounding("ceil"),
        ops.Floor: _rounding("floor"),
        ops.Round: _rounding("round"),
        ops.Equals: _compare("equal"),
        ops.NotEquals: _compare("not_equal"),
        ops.Less: _compare("lt"),
        ops.LessEqual: _compare("lte"),
        ops.Greater: _compare("gt"),
        ops.GreaterEqual: _compare("gte"),
        ops.IdenticalTo: _compare("is_not_distinct_from"),
        ops.And: lambda x, op: call("and", [x(op.left), x(op.right)]),
        ops.Or: lambda x, op: call("or", [x(op.left), x(op.right)]),
        ops.Not: _unary("not"),
        ops.IsNull: _unary("is_null"),
        ops.NotNull: _unary("is_not_null"),
        ops.Between: _between,
        ops.InValues: _in_values,
        ops.IfElse: _if_else,
        ops.SearchedCase: _searched_case,
        ops.SimpleCase: _simple_case,
        ops.Coalesce: _variadic("coalesce"),
        ops.Greatest: _variadic("greatest"),
        ops.Least: _variadic("least"),
        ops.NullIf: lambda x, op: call(
            "nullif", [x(op.arg, exact(op)), x(op.null_if_expr, exact(op))]
        ),
        ops.Clip: _clip,
        ops.IsNan: _is_nan,
        # Elementary functions of doubles (DataFusion converts integers) and
        # bitwise operations (`SubstraitLean/Numeric.lean`): the function table's.
        **table_rules("core", {"int.bit": _bitwise, "int.shift": _bitwise}),
        ops.Log: _log,
        # DataFusion's `COT(x)` is `1 / tan(x)` in IEEE division, so `cot(0)` is
        # `inf`; `DEGREES` and `RADIANS` multiply by Rust's constants
        # (`f64::to_degrees`, `to_radians`).
        ops.Cot: lambda x, op: ieee_divide(_double(1.0), call("tan", [x(op.arg, dt.float64)])),
        ops.Degrees: lambda x, op: call(
            "multiply", [x(op.arg, dt.float64), _double(180 / math.pi)]
        ),
        ops.Radians: lambda x, op: call(
            "multiply", [x(op.arg, dt.float64), _double(math.pi / 180)]
        ),
        ops.E: lambda x, op: _double(math.e),
        ops.Pi: lambda x, op: _double(math.pi),
        ops.Sign: _sign,
        ops.IsInf: _is_inf,
        # `~x` is `x XOR -1`, as Ibis's DataFusion SQL writes it.
        ops.BitwiseNot: lambda x, op: call("bitwise_xor", [x(op.arg), literal(-1, op.dtype)]),
        ops.Xor: _xor,
        DecimalDiv: _decimal_div,
    }
)


register_refusals(
    {
        "RandomScalar": _NONDETERMINISTIC,
        "RandomUUID": _NONDETERMINISTIC,
        "RowID": "the row id is the engine's own, so it differs between engines",
        "ScalarParameter": "bind it: pass params={param: value} to verify, which proves the "
        "transform for that value (an unbound parameter as any value of its type is planned: "
        "#354)",
    }
)

"""The lift's rules of logic, comparisons, conditionals, NULL handling,
arithmetic and math."""

from __future__ import annotations

import re
from collections.abc import Callable
from decimal import Decimal
from typing import Any

import ibis.expr.datatypes as dt
import sqlglot.expressions as sge

from sverify.plan_json import Json, Unsupported, if_then, literal
from sverify.sql_lift._base import (
    DUCKDB,
    Column,
    E,
    Sub,
    _decimal,
    _digits,
    _fn,
    _generated,
    _Lift,
    _numeric,
    _option,
    _overflow,
    _same,
    _shown,
    register,
)
from sverify.sql_lift.temporal import _temporal_literals, _temporal_plus

_COMPARISONS: dict[type, str] = {
    sge.EQ: "equal",
    sge.NEQ: "not_equal",
    sge.LT: "lt",
    sge.LTE: "lte",
    sge.GT: "gt",
    sge.GTE: "gte",
}

_ARITHMETIC: dict[type, str] = {sge.Add: "add", sge.Sub: "subtract", sge.Mul: "multiply"}
_SYMBOLS = {"add": "+", "subtract": "-", "multiply": "*"}


def _column(lf: _Lift, node: sge.Column, sub: Sub, scope: list[Column]) -> E:
    return lf.column(node, scope)


def _literal(lf: _Lift, node: sge.Literal, sub: Sub, scope: list[Column]) -> E:
    text = node.this
    if node.is_string:
        return E(literal(text, dt.string), dt.string, text)
    return _number(text)


def _number(text: str, negative: bool = False) -> E:
    """A number as DuckDB types it: the narrowest of `INTEGER` and `BIGINT`,
    a `DECIMAL(p, s)` with the digits as written, or a `DOUBLE` with an
    exponent or more than 38 digits."""
    sign = "-" if negative else ""
    if re.fullmatch(r"\d+", text):
        v = int(sign + text)
        for t in (dt.int32, dt.int64):
            if t.bounds.lower <= v <= t.bounds.upper:
                return E(literal(v, t), t, v)
        raise Unsupported(f"the integer {sign}{text} is a HUGEINT, which is not supported")
    m = re.fullmatch(r"(\d*)\.(\d*)", text)
    if m and len(m.group(1)) + len(m.group(2)) <= 38:
        v = Decimal(sign + text)
        t = _decimal(max(len(m.group(1)) + len(m.group(2)), 1), len(m.group(2)))
        return E(literal(v, t), t, v)
    v = float(sign + text)
    return E(literal(v, dt.float64), dt.float64, v)


def _boolean(lf: _Lift, node: sge.Boolean, sub: Sub, scope: list[Column]) -> E:
    return E(literal(bool(node.this), dt.boolean), dt.boolean, bool(node.this))


def _null(lf: _Lift, node: sge.Null, sub: Sub, scope: list[Column]) -> E:
    # Typed where it is used (`to`); alone, an INTEGER NULL.
    return E(literal(None, dt.int32), dt.null, None)


def _paren(lf: _Lift, node: sge.Paren, sub: Sub, scope: list[Column]) -> E:
    return sub(node.this)


def _neg(lf: _Lift, node: sge.Neg, sub: Sub, scope: list[Column]) -> E:
    inner = node.this
    if isinstance(inner, sge.Literal) and not inner.is_string:
        return _number(inner.this, negative=True)
    a = sub(inner)
    if not _numeric(a.type):
        raise Unsupported(f"-{a.type} is not supported")
    return E(_fn("negate", [a.json], a.type, _overflow(lf, a.type)), a.type)


def _arith(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
    name = _ARITHMETIC[type(node)]
    a, b = sub(node.this), sub(node.expression)
    if a.type.is_interval() or b.type.is_interval():
        return _temporal_plus(name, a, b)
    if name == "subtract" and a.type.is_date() and b.type.is_date():
        # DuckDB's DATE - DATE is a BIGINT of days.
        if a.midnight or b.midnight:
            raise Unsupported("a TIMESTAMP minus a DATE (an interval) is not supported yet")
        return E(_fn("date_diff", [a.json, b.json], dt.int64), dt.int64)
    if not (_numeric(a.type) or a.type.is_null()) or not (_numeric(b.type) or b.type.is_null()):
        raise Unsupported(f"{name} of {a.type} and {b.type} is not supported yet")
    t = lf.common([a, b], name, sum_digits=name != "multiply")
    if t.is_null():
        t = dt.int32
    if t.is_decimal():
        # The model computes decimals at their exact scales itself; the
        # output type is DuckDB's: `+`/`-` at the larger scale with one more
        # integer digit, `×` at the sum of the precisions and scales, but at
        # most 18 digits when both fit in 18 (a checked 64-bit product).
        (p1, s1), (p2, s2) = (
            _digits(lf.to(x, t).type if x.type.is_null() else x.type) for x in (a, b)
        )
        if name == "multiply":
            p = p1 + p2
            if p1 <= 18 and p2 <= 18 and p > 18:
                p = 18
            t = _decimal(p, s1 + s2)
        args = [x if not x.type.is_null() else lf.to(x, t) for x in (a, b)]
        return E(_fn(name, [x.json for x in args], t, _overflow(lf, t)), t)
    # DuckDB's: NaN for `inf - inf` and `0 * inf`, where the reference raises.
    if t.is_float64() and (g := _generated(lf, f"DOUBLE {_SYMBOLS[name]} DOUBLE", [a, b])):
        return g
    return E(_fn(name, [lf.to(a, t).json, lf.to(b, t).json], t, _overflow(lf, t)), t)


def _div(lf: _Lift, node: sge.Div, sub: Sub, scope: list[Column]) -> E:
    a, b = sub(node.this), sub(node.expression)
    for x in (a, b):
        if not (_numeric(x.type) or x.type.is_null()):
            raise Unsupported(f"/ of {a.type} and {b.type} is not supported")
    if node.args.get("typed") or node.args.get("safe"):
        raise Unsupported("typed or safe division is not DuckDB's /")
    # DuckDB's `/` divides as doubles (F1): integers as BIGINTs, decimals as
    # doubles; by zero it gives ±inf or NaN.
    ints = all(x.type.is_integer() or x.type.is_null() for x in (a, b))
    if g := _generated(lf, "BIGINT / BIGINT" if ints else "DOUBLE / DOUBLE", [a, b]):
        return g
    opt = _option("on_division_by_zero", lf.profile.float_division_by_zero)
    args = [lf.to(a, dt.float64).json, lf.to(b, dt.float64).json]
    return E(_fn("divide", args, dt.float64, [opt]), dt.float64)


def _int_div(lf: _Lift, node: sge.IntDiv, sub: Sub, scope: list[Column]) -> E:
    a, b = sub(node.this), sub(node.expression)
    t = lf.common([a, b], "//")
    if not t.is_integer():
        raise Unsupported(f"// of {a.type} and {b.type} is not supported; it divides integers")
    opts = [
        _option("overflow", lf.profile.overflow),
        _option("on_division_by_zero", lf.profile.on_division_by_zero),
    ]
    return E(_fn("divide", [lf.to(a, t).json, lf.to(b, t).json], t, opts), t)


def _mod(lf: _Lift, node: sge.Mod, sub: Sub, scope: list[Column]) -> E:
    a, b = sub(node.this), sub(node.expression)
    t = lf.common([a, b], "%")
    if t.is_float64():
        # DuckDB's: NaN by zero or of an infinity.
        if g := _generated(lf, "DOUBLE % DOUBLE", [a, b]):
            return g
        # sverify's own remainder of doubles, C's `fmod` (#256): Substrait's
        # `modulus` has no double impl.
        opt = _option("on_division_by_zero", "ERROR")
        return E(_fn("sverify_fmod", [lf.to(a, t).json, lf.to(b, t).json], t, [opt]), t)
    elif not t.is_integer():
        raise Unsupported(f"% of {a.type} and {b.type} is not supported yet")
    # The remainder takes the dividend's sign (`division_type` TRUNCATE, #209
    # R3), in DuckDB and the model.
    opts = [
        _option("on_division_by_zero", lf.profile.on_division_by_zero),
        _option("division_type", "TRUNCATE"),
    ]
    return E(_fn("modulus", [lf.to(a, t).json, lf.to(b, t).json], t, opts), t)


def _has_struct(t: Any) -> bool:
    """Whether `t` is a struct, or holds one."""
    if t.is_struct():
        return True
    if t.is_array():
        return _has_struct(t.value_type)
    if t.is_map():
        return _has_struct(t.key_type) or _has_struct(t.value_type)
    return False


def _operands(lf: _Lift, es: list[E], what: str) -> list[Json]:
    """Arguments of a comparison: decimals and integers as they are (the
    model compares them at a common scale), anything else at one type."""
    ts = [e.type for e in es if not e.type.is_null()]
    if any(t.is_decimal() for t in ts) and all(t.is_decimal() or t.is_integer() for t in ts):
        t = lf.common(es, what)
        return [(e if not e.type.is_null() else lf.to(e, t)).json for e in es]
    es = _temporal_literals(es)
    t = lf.common(es, what)
    if t.is_null():
        t = dt.int32
    return [lf.to(e, t).json for e in es]


def _compare(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
    name = _COMPARISONS[type(node)]
    a, b = sub(node.this), sub(node.expression)
    if name not in ("equal", "not_equal") and any(_has_struct(x.type) for x in (a, b)):
        # DuckDB orders structs field by field, NULLs last; the model's order
        # of structs is not that one yet. (Lists it orders as DuckDB does.)
        raise Unsupported(f"{_shown(node)}: ordering comparisons of {a.type} are not supported yet")
    args = _operands(lf, [a, b], name)
    return E(_fn(name, args, dt.boolean), dt.boolean)


def _logical(name: str) -> Callable[..., E]:
    def rule(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
        args = [sub(node.this), sub(node.expression)]
        for a in args:
            if not (a.type.is_boolean() or a.type.is_null()):
                raise Unsupported(f"{name.upper()} of a {a.type} is not supported")
        return E(_fn(name, [lf.to(a, dt.boolean).json for a in args], dt.boolean), dt.boolean)

    return rule


def _not(lf: _Lift, node: sge.Not, sub: Sub, scope: list[Column]) -> E:
    inner = node.this
    if isinstance(inner, sge.Is) and isinstance(inner.expression, sge.Null):
        return E(_fn("is_not_null", [sub(inner.this).json], dt.boolean), dt.boolean)
    a = sub(inner)
    if not (a.type.is_boolean() or a.type.is_null()):
        raise Unsupported(f"NOT of a {a.type} is not supported")
    return E(_fn("not", [lf.to(a, dt.boolean).json], dt.boolean), dt.boolean)


def _is(lf: _Lift, node: sge.Is, sub: Sub, scope: list[Column]) -> E:
    if not isinstance(node.expression, sge.Null):
        raise Unsupported(f"IS {_shown(node.expression)} is not supported; only IS [NOT] NULL is")
    return E(_fn("is_null", [sub(node.this).json], dt.boolean), dt.boolean)


def _between(lf: _Lift, node: sge.Between, sub: Sub, scope: list[Column]) -> E:
    if node.args.get("symmetric"):
        raise Unsupported("BETWEEN SYMMETRIC is not supported")
    x, lo, hi = _operands(
        lf, [sub(node.this), sub(node.args["low"]), sub(node.args["high"])], "BETWEEN"
    )
    both = [_fn("gte", [x, lo], dt.boolean), _fn("lte", [x, hi], dt.boolean)]
    return E(_fn("and", both, dt.boolean), dt.boolean)


def _in(lf: _Lift, node: sge.In, sub: Sub, scope: list[Column]) -> E:
    if node.args.get("unnest") is not None:
        raise Unsupported("IN UNNEST is not supported yet")
    if (query := node.args.get("query")) is not None:
        # SQL's NULLs: NULL when no value matches and the needle or a value
        # is NULL (the model lifts it so, `Parse.liftSubquery`).
        needle = sub(node.this)
        rel, cols = lf.nested(query, scope)
        if len(cols) != 1:
            raise Unsupported("an IN subquery must return one column")
        t = cols[0].type
        if not needle.type.is_null() and not _same(lf.common([needle, E({}, t)], "IN"), t):
            raise Unsupported(f"IN of a {needle.type} in a subquery of {t} is not supported yet")
        x = lf.to(needle, t).json
        return E({"subquery": {"inPredicate": {"needles": [x], "haystack": rel}}}, dt.boolean)
    es = [sub(node.this), *(sub(o) for o in node.expressions)]
    es = _temporal_literals(es)
    t = lf.common(es, "IN")
    if t.is_null():
        t = dt.int32
    value, *options = [lf.to(e, t).json for e in es]
    return E({"singularOrList": {"value": value, "options": options}}, dt.boolean)


def _case(lf: _Lift, node: sge.Case, sub: Sub, scope: list[Column]) -> E:
    ifs = node.args.get("ifs") or []
    base = node.this
    results = [sub(i.args["true"]) for i in ifs]
    default = node.args.get("default")
    dflt = sub(default) if default is not None else E(literal(None, dt.int32), dt.null, None)
    t = lf.common([*results, dflt], "CASE")
    if t.is_null():
        t = dt.int32
    conds = []
    for i in ifs:
        if base is not None:
            conds.append(_fn("equal", _operands(lf, [sub(base), sub(i.this)], "CASE"), dt.boolean))
        else:
            c = sub(i.this)
            if not (c.type.is_boolean() or c.type.is_null()):
                raise Unsupported(f"CASE WHEN {_shown(i.this)}: a {c.type}, not a condition")
            conds.append(lf.to(c, dt.boolean).json)
    pairs = [(c, lf.to(r, t).json) for c, r in zip(conds, results, strict=True)]
    midnight = t.is_date() and any(r.midnight for r in [*results, dflt])
    return E(if_then(pairs, lf.to(dflt, t).json), t, midnight=midnight)


def _coalesce(lf: _Lift, node: sge.Coalesce, sub: Sub, scope: list[Column]) -> E:
    es = [sub(node.this), *(sub(a) for a in node.expressions)]
    t = lf.common(es, "COALESCE")
    if t.is_null():
        t = dt.int32
    midnight = t.is_date() and any(e.midnight for e in es)
    return E(_fn("coalesce", [lf.to(e, t).json for e in es], t), t, midnight=midnight)


# -- numbers ------------------------------------------------------------------


def _prefer(name: str, value: str) -> Json:
    """An option preferring `value`, then ERROR: DuckDB's behaviour first,
    which the model may not support, and the reference's, which it does. A
    plan whose rows may meet the difference "may raise" (#185); where
    `verify` rules that out, the two agree."""
    prefs = [value] if value == "ERROR" else [value, "ERROR"]
    return {"name": name, "preference": prefs}


def _doubles(lf: _Lift, es: list[E], what: str) -> list[Json]:
    """Numbers as doubles, as DuckDB's elementary functions take them."""
    for e in es:
        if not (_numeric(e.type) or e.type.is_null()):
            raise Unsupported(f"{what} of a {e.type} is not supported")
    return [lf.to(e, dt.float64).json for e in es]


#: Elementary functions of doubles, by SQLGlot's node: the model's name.
_ELEMENTARY: dict[type, str] = {
    cls: name
    for cls, name in (
        (getattr(sge, n, None), name)
        for n, name in (
            ("Sqrt", "sqrt"),
            ("Exp", "exp"),
            ("Ln", "ln"),
            ("Sin", "sin"),
            ("Cos", "cos"),
            ("Tan", "tan"),
            ("Asin", "asin"),
            ("Acos", "acos"),
            ("Atan", "atan"),
        )
    )
    if cls is not None
}
_LOGS = ("ln", "log10", "log2", "logb")


def _elementary_call(lf: _Lift, name: str, args: list[Json]) -> E:
    opts = [_prefer("on_domain_error", lf.profile.domain_error)]
    if name in _LOGS:
        opts.append(_prefer("on_log_zero", lf.profile.log_zero))
    return E(_fn(name, args, dt.float64, opts), dt.float64)


def _elementary(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
    name = _ELEMENTARY[type(node)]
    return _elementary_call(lf, name, _doubles(lf, [sub(node.this)], name))


def _log(lf: _Lift, node: sge.Log, sub: Sub, scope: list[Column]) -> E:
    # DuckDB's `log(x)` is base 10, `log(b, x)` base b; `log2`, `log10`
    # are SQLGlot's `Log` with the base set.
    if node.expression is None:
        (x,) = _doubles(lf, [sub(node.this)], "log")
        if g := _generated(lf, "log(DOUBLE)", [E(x, dt.float64)]):
            return g
        return _elementary_call(lf, "log10", [x])
    base, x = node.this, node.expression
    if isinstance(base, sge.Literal) and base.this in ("2", "10"):
        return _elementary_call(lf, f"log{base.this}", _doubles(lf, [sub(x)], "log"))
    x_, b = _doubles(lf, [sub(x), sub(base)], "log")
    return _elementary_call(lf, "logb", [x_, b])


def _pow(lf: _Lift, node: sge.Pow, sub: Sub, scope: list[Column]) -> E:
    # DuckDB's `power` is of doubles, whatever its arguments.
    args = _doubles(lf, [sub(node.this), sub(node.expression)], "power")
    opts = [_prefer("on_domain_error", lf.profile.domain_error)]
    return E(_fn("power", args, dt.float64, opts), dt.float64)


def _abs(lf: _Lift, node: sge.Abs, sub: Sub, scope: list[Column]) -> E:
    a = sub(node.this)
    if not (_numeric(a.type) or a.type.is_null()):
        raise Unsupported(f"abs of a {a.type} is not supported")
    t = dt.int32 if a.type.is_null() else a.type
    return E(_fn("abs", [lf.to(a, t).json], t, _overflow(lf, t)), t)


def _rounding(name: str) -> Callable[..., E]:
    """`floor`, `ceil`, `round`: of a double, a double (an integer is one
    first for `floor` and `ceil`, as in DuckDB); `round` rounds halves away
    from zero, as DuckDB's of doubles does."""

    def rule(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
        a = sub(node.this)
        if a.type.is_decimal():
            raise Unsupported(f"{name} of a DECIMAL is not supported yet")
        digits = node.args.get("decimals") if name == "round" else None
        if name == "round" and a.type.is_integer() and digits is None:
            return a  # DuckDB's `round` of an integer is itself
        args = _doubles(lf, [a], name)
        if digits is not None:
            d = sub(digits)
            if not (d.constant and isinstance(d.value, int)):
                raise Unsupported("round needs a constant number of digits")
            if a.type.is_integer():
                raise Unsupported("round of an integer to digits is not supported yet")
            args.append(literal(d.value, dt.int32))
        return E(_fn(name, args, dt.float64), dt.float64)

    return rule


def _extremum(name: str) -> Callable[..., E]:
    def rule(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
        # DuckDB's `greatest` and `least` leave NULLs out.
        es = [sub(node.this), *(sub(a) for a in node.expressions)]
        t = lf.common(es, name)
        if t.is_null():
            t = dt.int32
        sql = "BIGINT" if t.is_int64() else "DOUBLE" if t.is_float64() else None
        if sql is not None and lf.profile is DUCKDB:
            # Of BIGINTs or DOUBLEs: the generated lift's, pairwise.
            g = es[0]
            for e in es[1:]:
                g = _generated(lf, f"{name}({sql}, {sql})", [lf.to(g, t), lf.to(e, t)])
                assert g is not None
            return g
        # Other types: pending generation (#268).
        return E(_fn(f"{name}_skip_null", [lf.to(e, t).json for e in es], t), t)

    return rule


def _nullif(lf: _Lift, node: sge.Nullif, sub: Sub, scope: list[Column]) -> E:
    a, b = sub(node.this), sub(node.expression)
    t = lf.common([a, b], "nullif")
    if t.is_null():
        t = dt.int32
    return E(_fn("nullif", [lf.to(a, t).json, lf.to(b, t).json], t), t)


def _sign(lf: _Lift, node: sge.Sign, sub: Sub, scope: list[Column]) -> E:
    # A TINYINT: -1, 0 or 1; 0 for NaN, as DuckDB's.
    a = sub(node.this)
    if not (_numeric(a.type) or a.type.is_null()) or a.type.is_decimal():
        raise Unsupported(f"sign of a {a.type} is not supported yet")
    sql = "DOUBLE" if a.type.is_float64() else "BIGINT"
    if g := _generated(lf, f"sign({sql})", [a]):
        return g
    t = dt.int64 if a.type.is_null() else a.type
    x = lf.to(a, t).json
    i8 = dt.int8
    ifs = [
        (_fn("lt", [x, literal(0, t)], dt.boolean), literal(-1, i8)),
        (_fn("gt", [x, literal(0, t)], dt.boolean), literal(1, i8)),
    ]
    if t.is_float64():
        ifs.insert(0, (_fn("is_nan", [x], dt.boolean), literal(0, i8)))
    null = _fn("is_null", [x], dt.boolean)
    return E(if_then([(null, literal(None, i8)), *ifs], literal(0, i8)), i8)


def _isnan(lf: _Lift, node: sge.IsNan, sub: Sub, scope: list[Column]) -> E:
    # NULL for NULL, as in DuckDB.
    (x,) = _doubles(lf, [sub(node.this)], "isnan")
    return E(_fn("is_nan", [x], dt.boolean), dt.boolean)


def _distinct_from(negate: bool) -> Callable[..., E]:
    def rule(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
        args = _operands(lf, [sub(node.this), sub(node.expression)], "IS DISTINCT FROM")
        same = _fn("is_not_distinct_from", args, dt.boolean)
        return E(_fn("not", [same], dt.boolean) if negate else same, dt.boolean)

    return rule


register(
    {
        sge.Column: _column,
        sge.Literal: _literal,
        sge.Boolean: _boolean,
        sge.Null: _null,
        sge.Paren: _paren,
        sge.Neg: _neg,
        sge.Add: _arith,
        sge.Sub: _arith,
        sge.Mul: _arith,
        sge.Div: _div,
        sge.IntDiv: _int_div,
        sge.Mod: _mod,
        sge.EQ: _compare,
        sge.NEQ: _compare,
        sge.LT: _compare,
        sge.LTE: _compare,
        sge.GT: _compare,
        sge.GTE: _compare,
        sge.And: _logical("and"),
        sge.Or: _logical("or"),
        sge.Not: _not,
        sge.Is: _is,
        sge.Between: _between,
        sge.In: _in,
        sge.Case: _case,
        sge.Coalesce: _coalesce,
        sge.Pow: _pow,
        sge.Abs: _abs,
        sge.Log: _log,
        sge.Floor: _rounding("floor"),
        sge.Ceil: _rounding("ceil"),
        sge.Round: _rounding("round"),
        sge.Greatest: _extremum("greatest"),
        sge.Least: _extremum("least"),
        sge.Nullif: _nullif,
        sge.Sign: _sign,
        sge.IsNan: _isnan,
        sge.NullSafeEQ: _distinct_from(False),
        sge.NullSafeNEQ: _distinct_from(True),
        **{cls: _elementary for cls in _ELEMENTARY},
    }
)

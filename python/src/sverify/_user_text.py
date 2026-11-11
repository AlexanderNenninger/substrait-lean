"""Lean's expressions in the user's terms (#655): column names for the
positional `$i`, and the Ibis or SQL operator for Lean's (`/.`, `DOUBLE(…)`).

Internal: not part of sverify's public API.

The checker names an operation by `Expr.render` (`SubstraitLean/Pretty.lean`),
where `$i` is the i-th column of the input of the relation the operation is
in. The plan (Substrait protobuf JSON) says which columns each relation's
input has: `columns` walks it, and `user_expr` names `$i` where every
relation that reads all of the expression's columns gives them the same
names. Where it cannot tell, the expression keeps Lean's notation.
"""

from __future__ import annotations

import json
import re
from collections.abc import Collection, Mapping, Sequence
from datetime import date, datetime, timedelta
from typing import Any, Literal

from sverify import _plan_read

Dialect = Literal["ibis", "sql"]

#: The relation types whose output is their input's columns, unchanged.
_PASS = ("filter", "sort", "fetch")


def _refs(node: Any, out: set[int]) -> None:
    """The input columns an expression reads (`selection` from the root)."""
    if isinstance(node, dict):
        sel = node.get("selection")
        if isinstance(sel, dict) and "rootReference" in sel:
            f = ((sel.get("directReference") or {}).get("structField") or {}).get("field", 0)
            out.add(int(f))
        for v in node.values():
            _refs(v, out)
    elif isinstance(node, list):
        for v in node:
            _refs(v, out)


def _field(e: Any) -> int | None:
    """The column an expression is, if it is one (through casts)."""
    while isinstance(e, dict) and "cast" in e:
        e = e["cast"].get("input")
    sel = e.get("selection") if isinstance(e, dict) else None
    if isinstance(sel, dict) and "rootReference" in sel:
        return int(((sel.get("directReference") or {}).get("structField") or {}).get("field", 0))
    return None


Seen = list[tuple[list[Any], set[int], dict[int, list[str]], set[tuple[int, ...]]]]


def _pairs(node: Any, out: set[tuple[int, ...]]) -> None:
    """The column arguments of each function call in an expression whose
    arguments are all columns: `($1 - $3)` is `(1, 3)`."""
    if isinstance(node, dict):
        fn = node.get("scalarFunction")
        if isinstance(fn, dict):
            args = [_field((a or {}).get("value")) for a in fn.get("arguments") or []]
            if args and all(a is not None for a in args):
                out.add(tuple(args))  # type: ignore[arg-type]
        for v in node.values():
            _pairs(v, out)
    elif isinstance(node, list):
        for v in node:
            _pairs(v, out)


class _Slot:
    """A column a relation computes: named once the plan's output names show
    that it reaches the output unchanged (`columns`)."""

    __slots__ = ("name",)

    def __init__(self) -> None:
        self.name: str | None = None


def _name(v: Any) -> str | None:
    return v.name if isinstance(v, _Slot) else v


def columns(plan: Mapping[str, Any]) -> Seen:
    """Each relation that computes expressions, as its input's column names
    (None where unknown), the input columns its expressions read, and, for
    an aggregate, the measures over each column (`sum(x)`)."""
    fns = _plan_read.function_names(plan)
    out: Seen = []

    def emit(rel: dict, names: list[Any]) -> list[Any]:
        mapping = ((rel.get("common") or {}).get("emit") or {}).get("outputMapping")
        if mapping is None:
            return names
        return [names[i] if i < len(names) else _Slot() for i in mapping]

    def record(inp: list[Any] | None, exprs: Any, measures=None) -> None:
        reads: set[int] = set()
        _refs(exprs, reads)
        pairs: set[tuple[int, ...]] = set()
        _pairs(exprs, pairs)
        # An input whose names are not known is kept, as `[]`: a relation
        # that reads the columns makes their names ambiguous.
        out.append((inp or [], reads, measures or {}, pairs))

    def at(inp: list[Any] | None, e: Any) -> Any:
        if inp is None:
            return _Slot()
        f = _field(e)
        if f is not None:
            return inp[f] if f < len(inp) else _Slot()
        # A window function over columns: `lag(ts)`, `sum(new_session)`.
        win = e.get("windowFunction") if isinstance(e, dict) else None
        if isinstance(win, dict):
            name = _plan_read.base_name(fns.get(win.get("functionReference", 0), "?"))
            args = []
            for a in win.get("arguments") or []:
                v = a.get("value") if isinstance(a, dict) else None
                if (g := _field(v)) is not None and g < len(inp) and _name(inp[g]) is not None:
                    args.append(_name(inp[g]))
                elif isinstance(v, dict) and "literal" in v:
                    continue
                else:
                    return _Slot()
            return f"{name}({', '.join(args)})"  # type: ignore[arg-type]
        return _Slot()

    def walk(node: Any) -> list[Any] | None:
        if not isinstance(node, dict) or len(node) != 1:
            return None
        kind, rel = next(iter(node.items()))
        if not isinstance(rel, dict):
            return None
        if kind == "read":
            names: list[Any] = list((rel.get("baseSchema") or {}).get("names") or [])
            return emit(rel, names)
        if kind in ("join", "cross"):
            left, right = walk(rel.get("left")), walk(rel.get("right"))
            joined = None if left is None or right is None else left + right
            if "expression" in rel:
                record(joined, rel["expression"])
            return None if joined is None else emit(rel, joined)
        if kind == "set":
            ins = [walk(i) for i in rel.get("inputs") or []]
            return None if not ins or ins[0] is None else emit(rel, ins[0])
        inp = walk(rel.get("input"))
        if kind in _PASS:
            if kind == "filter":
                record(inp, rel.get("condition"))
            elif kind == "sort":
                record(inp, rel.get("sorts"))
            return None if inp is None else emit(rel, inp)
        if kind == "project":
            exprs = rel.get("expressions") or []
            record(inp, exprs)
            if inp is None:
                return None
            return emit(rel, inp + [at(inp, e) for e in exprs])
        if kind == "aggregate":
            measures: dict[int, list[str]] = {}
            for m in rel.get("measures") or []:
                fn = (m or {}).get("measure") or {}
                args = fn.get("arguments") or []
                if len(args) == 1 and (f := _field(args[0].get("value"))) is not None:
                    name = _plan_read.base_name(fns.get(fn.get("functionReference", 0), "?"))
                    measures.setdefault(f, []).append(name)
            record(inp, {k: v for k, v in rel.items() if k != "input"}, measures)
            keys = [at(inp, g) for g in rel.get("groupingExpressions") or []]
            if not rel.get("groupingExpressions"):
                keys = [
                    at(inp, e)
                    for g in rel.get("groupings") or []
                    for e in g.get("groupingExpressions") or []
                ]
            if inp is None:
                return None
            return emit(rel, keys + [_Slot() for _ in rel.get("measures") or []])
        # Windows, unnests, extensions: their expressions are read, but what
        # they output is not followed.
        record(inp, {k: v for k, v in rel.items() if k != "input"})
        return None

    text = json.dumps(plan)
    if '"subquery"' in text or '"lambda"' in text:
        # Relations inside expressions are not walked, and a lambda's body
        # numbers its parameters as Lean numbers columns: no name is sure.
        return [([], set(range(10_000)), {}, set())]
    for r in plan.get("relations") or []:
        root = r.get("root") or {}
        names = walk(root.get("input") or r.get("rel") or {})
        # A column computed on the way that reaches the output unchanged has
        # the output's name.
        for v, name in zip(names or [], root.get("names") or [], strict=False):
            if isinstance(v, _Slot) and v.name is None:
                v.name = name
    return out


_FIELD = re.compile(r"\$(\d+)")


def _names(expr: str, seen: Seen) -> tuple[dict[int, str], dict[int, list[str]]] | None:
    """The names of the columns `expr` reads, where every relation that
    reads them all agrees, with that relation's measures."""
    wanted = {int(i) for i in _FIELD.findall(expr)}
    if not wanted:
        return {}, {}
    candidates = [x for x in seen if wanted <= x[1]]
    # A call on columns only (`($1 - $3)`) is in a relation that makes it.
    calls = {
        tuple(int(i) for i in _FIELD.findall(m)) for m in re.findall(r"\((\$\d+ \S+ \$\d+)\)", expr)
    }
    if calls and (making := [x for x in candidates if calls & x[3]]):
        candidates = making
    found: list[tuple[dict[int, str], dict[int, list[str]]]] = []
    for names, _reads, measures, _calls in candidates:
        if any(i >= len(names) or _name(names[i]) is None for i in wanted):
            return None
        found.append(({i: _name(names[i]) for i in wanted}, measures))  # type: ignore[misc]
    if not found or any(f[0] != found[0][0] for f in found):
        return None
    return found[0]


#: Lean's binary operators (`Functions.prettyOf`) as the user writes them.
_OPS: dict[Dialect, dict[str, str]] = {
    "ibis": {
        "/.": "/", "/": "//", "/ROUND": "/", "*.": "*", "+.": "+", "-.": "-",
        "%.": "%", "^.": "**", "^": "**", "=": "==", "AND": "&", "OR": "|", "||": "+",
    },
    "sql": {
        "/.": "/", "/ROUND": "/", "*.": "*", "+.": "+", "-.": "-", "%.": "%", "^.": "^",
    },
}  # fmt: skip


def _strip(s: str) -> str:
    """`s` without the parentheses around the whole of it."""
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        for i, c in enumerate(s):
            depth += c == "("
            depth -= c == ")"
            if depth == 0 and i < len(s) - 1:
                return s
        s = s[1:-1]
    return s


def _measure(expr: str, seen: Seen) -> str | None:
    """A bare column `$i` that exactly one aggregate adds up, as its measure
    (`sum(amount)`): a `SUM` overflow names the column the measure reads, in
    the aggregate's input, which relations after it may number otherwise."""
    m = _FIELD.fullmatch(expr)
    if m is None:
        return None
    i = int(m[1])
    found = {
        " or ".join(dict.fromkeys(f"{_AGG_NAMES.get(f, f)}({_name(names[i])})" for f in fs))
        for names, _, measures, _calls in seen
        if (fs := [f for f in measures.get(i, []) if f not in _NO_OVERFLOW])
        and i < len(names)
        and _name(names[i]) is not None
    }
    return found.pop() if len(found) == 1 else None


#: Aggregates that cannot leave their argument's range.
_NO_OVERFLOW = frozenset({"min", "max", "count", "first", "last", "any_value", "mode"})

#: Substrait's names of aggregates where Ibis's differ.
_AGG_NAMES = {"avg": "mean", "std_dev": "std", "variance": "var"}


def named(
    expr: str, plan: Mapping[str, Any] | None, measure: bool = False, seen: Seen | None = None
) -> str | None:
    """`expr` (Lean's notation) with column names for `$i`, Lean's operators
    kept; None where the plan does not say which columns it reads. With
    `measure`, a bare column an aggregate adds up is its measure, `sum(x)`
    (`_measure`)."""
    if plan is None:
        return None
    seen = columns(plan) if seen is None else seen
    if measure and (sum_of := _measure(expr, seen)) is not None:
        return sum_of
    found = _names(expr, seen)
    if found is None:
        return None
    names, measures = found
    # A bare column an aggregate adds up is named by its measure: `sum(x)`.
    if (m := _FIELD.fullmatch(expr)) and len(measures.get(int(m[1]), [])) == 1:
        f = measures[int(m[1])][0]
        return f"{_AGG_NAMES.get(f, f)}({names[int(m[1])]})"
    return _FIELD.sub(lambda m: names[int(m[1])], expr)


def _decimal(dialect: Dialect, x: str, p: str, s: str) -> str:
    if dialect == "ibis":
        return f"{x}.cast('decimal({p}, {s})')"
    return f"CAST({x} AS DECIMAL({p}, {s}))"


def pretty(
    out: str,
    dialect: Dialect = "ibis",
    temporal: Collection[str] = (),
) -> str:
    """A named expression (`named`) with the user's operators and casts:
    `/` of integers as Ibis's `//`, `DECIMAL_10_2(TO_DECIMAL_2(x))` as the
    cast the user wrote, a timestamp plus microseconds as an interval
    (`temporal` names the timestamp columns), no implicit casts."""
    # Implicit casts the user did not write.
    while (new := re.sub(r"\b(?:DOUBLE|AS_DECIMAL_\d+_\d+)\(([^()]*)\)", r"\1", out)) != out:
        out = new
    out = re.sub(r"(\d)d\b", r"\1", out)
    # A cast to a decimal: `DECIMAL_p_s(TO_DECIMAL_s(x))` (a double's), or
    # `DECIMAL_p_s(x)`, `TO_DECIMAL_s(x)` alone (the precision is the plan's).
    out = re.sub(
        r"\bDECIMAL_(\d+)_(\d+)\(TO_DECIMAL_\d+\(([^()]*)\)\)",
        lambda m: _decimal(dialect, m[3], m[1], m[2]),
        out,
    )
    out = re.sub(
        r"\bDECIMAL_(\d+)_(\d+)\(([^()]*)\)", lambda m: _decimal(dialect, m[3], m[1], m[2]), out
    )
    out = re.sub(
        r"\bTO_DECIMAL_(\d+)\(([^()]*)\)", lambda m: _decimal(dialect, m[2], "…", m[1]), out
    )
    trunc = r"\b(?:DATE|DAY)_TRUNC_(\w+)\(([^()]*)\)"
    if dialect == "ibis":
        out = re.sub(trunc, lambda m: f"{m[2]}.truncate({m[1].lower()!r})", out)
    else:
        out = re.sub(trunc, lambda m: f"date_trunc('{m[1].lower()}', {m[2]})", out)
    if temporal:
        cols = "|".join(re.escape(c) for c in sorted(temporal, key=len, reverse=True))
        out = re.sub(
            rf"(?<![\w.])({cols}) ([+-]) (-?\d+)\b",
            lambda m: f"{m[1]} {m[2]} {interval_text(int(m[3]), dialect)}",
            out,
        )
    ops = _OPS[dialect]
    pattern = "|".join(re.escape(k) for k in sorted(ops, key=len, reverse=True))
    out = re.sub(rf"(?<= )(?:{pattern})(?= )", lambda m: ops[m[0]], out)
    return _strip(_unparen(out))


#: The binding of the arithmetic operators, the same in Python and SQL.
_BINDS = {"+": 1, "-": 1, "*": 2, "/": 2, "//": 2, "%": 2}


def _unparen(s: str) -> str:
    """`s` without the parentheses arithmetic does not need: the left
    operand of an operator that binds as tightly, or an operand that binds
    tighter (`((a - b) * 100) // c` is `(a - b) * 100 // c`)."""
    p = split_bin(s)
    if p is None:
        return s
    a, op, b = _unparen(p[0]), p[1], _unparen(p[2])
    if op in _BINDS:
        if (q := split_bin(a)) and q[1] in _BINDS and _BINDS[q[1]] >= _BINDS[op]:
            a = a[1:-1]
        if (q := split_bin(b)) and q[1] in _BINDS and _BINDS[q[1]] > _BINDS[op]:
            b = b[1:-1]
    return f"({a} {op} {b})"


def interval_text(us: int, dialect: Dialect = "ibis") -> str:
    """Microseconds as the interval the user wrote: `ibis.interval(minutes=5)`,
    `INTERVAL 5 MINUTE`."""
    for name, unit in _UNITS:
        n = unit // timedelta(microseconds=1)
        if us % n == 0:
            k = us // n
            if dialect == "ibis":
                return f"ibis.interval({name}={k})"
            sql = name.upper().removesuffix("S")
            return f"INTERVAL {k} {sql}"
    return str(us)  # pragma: no cover - every count of microseconds has a unit


def user_expr(
    expr: str,
    plan: Mapping[str, Any] | None,
    dialect: Dialect = "ibis",
    temporal: Collection[str] = (),
    measure: bool = False,
) -> str | None:
    """`expr` (Lean's notation) with column names and the user's operators;
    None where the plan does not say which columns it reads."""
    out = named(expr, plan, measure)
    return None if out is None else pretty(out, dialect, temporal)


# -- one issue per expression the user wrote -----------------------------------


def split_bin(s: str) -> tuple[str, str, str] | None:
    """`(a op b)`, as Lean renders a binary operation, as `(a, op, b)`; None
    for anything else."""
    if not (s.startswith("(") and s.endswith(")")) or _strip(s) == s:
        return None
    inner = s[1:-1]

    def operand_end(t: str, i: int) -> int | None:
        depth, quoted = 0, False
        while i < len(t):
            c = t[i]
            if quoted:
                if c == "\\":
                    i += 1
                elif c == '"':
                    quoted = False
            elif c == '"':
                quoted = True
            elif c in "([":
                depth += 1
            elif c in ")]":
                depth -= 1
                if depth < 0:
                    return None
            elif c == " " and depth == 0:
                return i
            i += 1
        return None

    a_end = operand_end(inner, 0)
    if a_end is None:
        return None
    op_end = inner.find(" ", a_end + 1)
    if op_end < 0:
        return None
    a, op, b = inner[:a_end], inner[a_end + 1 : op_end], inner[op_end + 1 :]
    return (a, op, b) if a and op and b else None


def _minus_one(s: str) -> str | None:
    """`x` of `(x - 1)` or `(x + -1)`."""
    p = split_bin(s)
    if p and ((p[1] == "-" and p[2] == "1") or (p[1] == "+" and p[2] == "-1")):
        return p[0]
    return None


def floor_fold(s: str) -> str:
    """`s` with the reference's form of a floor division or modulus
    (`Expr.floorDivOf`, `floorModOf` in `core/Sverify/Core/Expr.lean`) as the
    `a / b` or `a % b` the user wrote, wherever `s` is one of its branches:
    `(((a + 1) / b) - 1)`, `((a - 1) / b)`, `((b - 1) - ((-1 - a) % b))`,
    `(((a - 1) % b) + (b + 1))`."""
    p = split_bin(s)
    if p is None:
        return s
    a, op, b = floor_fold(p[0]), p[1], floor_fold(p[2])
    if op in ("-", "+") and (x := _minus_one(s)) is not None:
        q = split_bin(x)
        if q and q[1] == "/" and (r := split_bin(q[0])) and r[1] in "+-" and r[2] == "1":
            return f"({floor_fold(r[0])} / {floor_fold(q[2])})"
    if op == "/" and (r := split_bin(a)) and r[1] in ("+", "-") and r[2] == "1":
        return f"({r[0]} / {b})"
    if op == "-" and (r := split_bin(b)) and r[1] == "%":
        dividend = split_bin(r[0])
        if dividend and dividend[:2] == ("-1", "-") and a == f"({r[2]} - 1)":
            return f"({dividend[2]} % {r[2]})"
    if op == "+" and (r := split_bin(a)) and r[1] == "%" and b == f"({r[2]} + 1)":
        dividend = split_bin(r[0])
        if dividend and dividend[1:] == ("-", "1"):
            return f"({dividend[0]} % {r[2]})"
    return f"({a} {op} {b})"


def fold(exprs: Sequence[str], floor: bool) -> list[str]:
    """For each expression (of one kind of issue), the expression it is
    reported under: the largest of `exprs` that contains it, after
    `floor_fold` where the plan divides with `division_type` FLOOR. The
    sub-expressions of one expression the user wrote, and the branches of
    the reference's form of a floor division, become one."""
    shown = [floor_fold(e) if floor else e for e in exprs]
    out = []
    for e, f in zip(exprs, shown, strict=True):
        best = max(
            (j for j, (g, h) in enumerate(zip(exprs, shown, strict=True)) if e in g or f in h),
            key=lambda j: (len(exprs[j]), -j),
        )
        out.append(shown[best])
    return out


# -- conditions as the user wrote them -----------------------------------------

_UNITS = (
    ("weeks", timedelta(weeks=1)),
    ("days", timedelta(days=1)),
    ("hours", timedelta(hours=1)),
    ("minutes", timedelta(minutes=1)),
    ("seconds", timedelta(seconds=1)),
    ("milliseconds", timedelta(milliseconds=1)),
    ("microseconds", timedelta(microseconds=1)),
)

_IBIS_UNITS = {
    "YEAR": "years",
    "QUARTER": "quarters",
    "MONTH": "months",
    "WEEK": "weeks",
    "DAY": "days",
    "HOUR": "hours",
    "MINUTE": "minutes",
    "SECOND": "seconds",
    "MILLISECOND": "milliseconds",
    "MICROSECOND": "microseconds",
    "NANOSECOND": "nanoseconds",
}


def value_text(v: Any) -> str:
    """A Python value as the user would write it: `datetime(9999, 1, 1)`,
    `date(2024, 1, 31)`, `timedelta(minutes=5)`, `ibis.interval(minutes=5)`."""
    if isinstance(v, datetime):
        parts = [v.year, v.month, v.day, v.hour, v.minute, v.second, v.microsecond]
        while len(parts) > 3 and parts[-1] == 0:
            parts.pop()
        return f"datetime({', '.join(map(str, parts))})"
    if isinstance(v, date):
        return f"date({v.year}, {v.month}, {v.day})"
    if isinstance(v, timedelta):
        if not v:
            return "timedelta(0)"
        for name, unit in _UNITS:
            if v % unit == timedelta(0):
                return f"timedelta({name}={v // unit})"
    import ibis.expr.operations as ops
    import ibis.expr.types as ir

    if isinstance(v, ir.Expr) and isinstance(op := v.op(), ops.Literal):
        if op.dtype.is_interval():
            unit = _IBIS_UNITS.get(op.dtype.unit.name, op.dtype.unit.name.lower())
            return f"ibis.interval({unit}={op.value})"
        return value_text(op.value)
    if hasattr(v, "__deferred_repr__"):
        return v.__deferred_repr__()
    return getattr(v, "__name__", None) or repr(v)


def deferred_text(d: Any) -> str:
    """An Ibis deferred condition (`_.ts < datetime(9999, 1, 1)`) as written,
    with its values in Python's short forms (`value_text`) where Ibis's own
    repr shows `datetime.datetime(9999, 1, 1, 0, 0)` or
    `<scalar[interval('m')]>`."""
    from ibis.common import deferred as dd

    def go(r: Any) -> str:
        if isinstance(r, dd.Deferred):
            return go(r._resolver)
        if isinstance(r, dd.Just | dd.JustUnhashable):
            return value_text(getattr(r, "value", None))
        if isinstance(r, dd.Attr) and isinstance(r.name, dd.Just):
            return f"{go(r.obj)}.{r.name.value}"
        if isinstance(r, dd.Item) and isinstance(r.indexer, dd.Just):
            return f"{go(r.obj)}[{r.indexer.value!r}]"
        if isinstance(r, dd.Call):
            args = [go(a) for a in r.args] + [f"{k}={go(v)}" for k, v in r.kwargs.items()]
            return f"{go(r.func)}({', '.join(args)})"
        if isinstance(r, dd.UnaryOperator):
            return f"{dd._operator_symbols[r.func]}{go(r.arg)}"
        if isinstance(r, dd.BinaryOperator):
            return f"({go(r.left)} {dd._operator_symbols[r.func]} {go(r.right)})"
        if isinstance(r, dd.Sequence):
            elems = ", ".join(go(v) for v in getattr(r, "values", ()))
            return f"({elems})" if getattr(r, "typ", list) is tuple else f"[{elems}]"
        return repr(r)

    try:
        return go(d)
    except Exception:  # noqa: BLE001 - a label falls back to Ibis's repr
        return repr(d)

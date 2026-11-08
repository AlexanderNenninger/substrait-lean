"""Export a verified plan to any Substrait consumer, with its contract (#664).

`Report.to_substrait` returns the plan the checker verified, written for a
conforming consumer of Substrait 0.106:

- every function call names its YAML's URN, its compound name
  (`add:i64_i64`) and its output type (`_substrait_extensions.json`, from
  the YAMLs);
- every option the proof depends on (`Report.depends`) is pinned in the
  call's options, at the reference's behaviour, so the consumer cannot
  choose differently (`overflow`, `rounding`, `on_division_by_zero`, …);
- where Substrait has no option for a choice the proof uses (a spec gap,
  `upstream/bugs/ST-*.json`), the gap is handled in one of three ways:
  the reference raises there, and the contract's preconditions rule those
  inputs out (`unexercised`); the plan is rewritten into well-specified
  Substrait (`shims`); or the consumer's result equals the reference's up
  to an observation the postconditions allow (`up_to`). Otherwise the
  export is refused with the gap named (`ExportError`).

The contract travels in the plan's `advanced_extensions.optimization` as an
`io.sverify.substrait.v1.Contract` message (`contract.proto`, next to this
module): the preconditions, declared and inferred, and the postconditions,
each in the user's terms and as a Substrait plan, and a manifest. A consumer
that does not know the message ignores it, as Substrait's docs allow for an
optimization. `from_substrait` reads both back and proves the contract again
with the checker.
"""

from __future__ import annotations

import copy
import dataclasses
import functools
import json
import re
from collections.abc import Mapping, Sequence
from datetime import timedelta
from importlib import resources
from typing import TYPE_CHECKING, Any, Literal

from sverify import _meta
from sverify._unsupported import SverifyError

if TYPE_CHECKING:
    from sverify.report import Report

#: The Substrait version the export writes, the one `Profile.substrait` reads.
SUBSTRAIT_VERSION = (0, 106, 0)
#: The protobuf package and type URL of the contract message.
PACKAGE = "io.sverify.substrait.v1"
TYPE_URL = f"type.googleapis.com/{PACKAGE}.Contract"
#: The version of the manifest's format. Format 2 (1.0) says `semantics`
#: and `equivalence` where format 1 said `profile` and `observation`; `read`
#: reads both.
FORMAT = 2

Json = dict[str, Any]
Format = Literal["json", "binary"]
Shims = Literal["apply", "annotate", "refuse"]
SHIMS: tuple[Shims, ...] = ("apply", "annotate", "refuse")

#: The spec gaps behind the options Substrait leaves open
#: (`SubstraitLean/SubstraitProfile.lean`, `docs/core-semantics.md`).
GAPS: Mapping[str, str] = {
    "shift_range": "ST-1",
    "stat_degenerate": "ST-3",
    "nan_equality": "ST-4",
    "nan_order": "ST-4",
    "nan_creation": "ST-5",
    "float_to_int": "ST-6",
    "cast_failure": "ST-6",
    "null_order": "ST-7",
    "decimal_rescale": "ST-8",
    "float_overflow": "ST-9",
}
#: Functions whose meaning a spec gap leaves open whatever the options say.
FUNCTION_GAPS: Mapping[str, str] = {"upper": "ST-10", "lower": "ST-10"}
#: sverify's names of Substrait functions whose YAML names differ, where the
#: two mean the same.
ALIASES: Mapping[str, str] = {
    "bitwise_shift_left": "shift_left",
    "bitwise_shift_right": "shift_right",
    "character_length": "char_length",
    "btrim": "trim",
    "str_concat": "concat",
}


class ExportError(SverifyError, ValueError):
    """The plan has no conforming Substrait form that keeps its proof: the
    message names the reason, and the spec gap where there is one."""

    code = "export_refused"


# -- the YAML table -----------------------------------------------------------


@functools.cache
def _extensions() -> dict[str, list[Json]]:
    text = resources.files("sverify").joinpath("_substrait_extensions.json").read_text()
    return json.loads(text)["functions"]


# -- types --------------------------------------------------------------------

#: Substrait JSON type keys, as the YAMLs name them.
_JSON_TO_YAML = {
    "bool": "boolean",
    "i8": "i8",
    "i16": "i16",
    "i32": "i32",
    "i64": "i64",
    "fp32": "fp32",
    "fp64": "fp64",
    "string": "string",
    "binary": "binary",
    "date": "date",
    "intervalYear": "interval_year",
    "intervalDay": "interval_day",
    "intervalCompound": "interval_compound",
    "uuid": "uuid",
    "fixedChar": "fixedchar",
    "varchar": "varchar",
    "fixedBinary": "fixedbinary",
    "decimal": "decimal",
    "precisionTime": "precision_time",
    "precisionTimestamp": "precision_timestamp",
    "precisionTimestampTz": "precision_timestamp_tz",
    "struct": "struct",
    "list": "list",
    "map": "map",
}
_YAML_TO_JSON = {v: k for k, v in _JSON_TO_YAML.items()}

#: The short names of the compound function names (Substrait's
#: `extensions/index.md`).
_SHORT = {
    "boolean": "bool",
    "i8": "i8",
    "i16": "i16",
    "i32": "i32",
    "i64": "i64",
    "fp32": "fp32",
    "fp64": "fp64",
    "string": "str",
    "binary": "vbin",
    "timestamp": "ts",
    "timestamp_tz": "tstz",
    "date": "date",
    "time": "time",
    "interval_year": "iyear",
    "interval_day": "iday",
    "interval_compound": "icompound",
    "uuid": "uuid",
    "fixedchar": "fchar",
    "varchar": "vchar",
    "fixedbinary": "fbin",
    "decimal": "dec",
    "precision_time": "pt",
    "precision_timestamp": "pts",
    "precision_timestamp_tz": "ptstz",
    "struct": "struct",
    "list": "list",
    "map": "map",
}


#: The types with a `precision` parameter.
_PRECISIONED = frozenset(
    {"precision_time", "precision_timestamp", "precision_timestamp_tz", "interval_day"}
)


@dataclasses.dataclass(frozen=True)
class Ty:
    """A type: its YAML name and parameters (integers or types)."""

    name: str
    params: tuple[Any, ...] = ()

    def json(self) -> Json:
        key = _YAML_TO_JSON.get(self.name)
        if key is None:
            raise ExportError(f"to_substrait cannot write the type {self.name}")
        body: Json = {"nullability": "NULLABILITY_NULLABLE"}
        p = self.params
        if self.name == "decimal":
            body.update(precision=p[0], scale=p[1])
        elif self.name in _PRECISIONED:
            body["precision"] = p[0] if p else 6
        elif self.name in ("varchar", "fixedchar", "fixedbinary"):
            body["length"] = p[0]
        elif self.name == "list":
            body["type"] = p[0].json()
        elif self.name == "struct":
            body["types"] = [t.json() for t in p]
        elif self.name == "map":
            body.update(key=p[0].json(), value=p[1].json())
        return {key: body}


def ty_of(j: Json) -> Ty:
    """A Substrait JSON type as a `Ty`."""
    [(key, body)] = [(k, v) for k, v in j.items() if k != "typeVariationReference"]
    name = _JSON_TO_YAML.get(key)
    if name is None:
        raise ExportError(f"to_substrait cannot read the type {key}")
    body = body or {}
    if name == "decimal":
        return Ty(name, (int(body.get("precision", 0)), int(body.get("scale", 0))))
    if name in ("precision_time", "precision_timestamp", "precision_timestamp_tz", "interval_day"):
        return Ty(name, (int(body.get("precision", 6)),))
    if name in ("varchar", "fixedchar", "fixedbinary"):
        return Ty(name, (int(body.get("length", 0)),))
    if name == "list":
        return Ty(name, (ty_of(body["type"]),))
    if name == "struct":
        return Ty(name, tuple(ty_of(t) for t in body.get("types", [])))
    if name == "map":
        return Ty(name, (ty_of(body["key"]), ty_of(body["value"])))
    return Ty(name)


# -- the YAMLs' type expressions ---------------------------------------------

_TOKEN = re.compile(r"\s*(\d+|[A-Za-z_!][A-Za-z_0-9!]*|&&|\|\||[<>=!]=|[-+*/(),?:<>!])")


def _tokens(s: str) -> list[str]:
    out, i = [], 0
    s = s.strip()
    while i < len(s):
        m = _TOKEN.match(s, i)
        if not m:
            raise ExportError(f"cannot read the YAML expression {s!r}")
        out.append(m.group(1))
        i = m.end()
    return out


class _Expr:
    """A recursive-descent reader of the YAMLs' derivation expressions: types
    (`decimal<P1,S1>`, `any1`, `list<any1>`), integers, `min`/`max`, the
    arithmetic and comparison operators and `c ? a : b`."""

    def __init__(self, text: str, env: Mapping[str, Any]):
        self.t = _tokens(text)
        self.i = 0
        self.env = env

    def peek(self) -> str | None:
        return self.t[self.i] if self.i < len(self.t) else None

    def take(self, tok: str | None = None) -> str:
        cur = self.peek()
        if cur is None or (tok is not None and cur != tok):
            raise ExportError(f"cannot read the YAML expression {' '.join(self.t)!r}")
        self.i += 1
        return cur

    def expr(self) -> Any:
        c = self.disj()
        if self.peek() == "?":
            self.take("?")
            a = self.expr()
            self.take(":")
            b = self.expr()
            return a if c else b
        return c

    def disj(self) -> Any:
        v = self.conj()
        while self.peek() == "||":
            self.take()
            w = self.conj()
            v = bool(v) or bool(w)
        return v

    def conj(self) -> Any:
        v = self.cmp()
        while self.peek() == "&&":
            self.take()
            w = self.cmp()
            v = bool(v) and bool(w)
        return v

    def cmp(self) -> Any:
        v = self.add()
        ops = {
            "<": lambda a, b: a < b,
            ">": lambda a, b: a > b,
            "<=": lambda a, b: a <= b,
            ">=": lambda a, b: a >= b,
            "==": lambda a, b: a == b,
            "!=": lambda a, b: a != b,
        }
        if self.peek() in ops:
            op = ops[self.take()]
            return op(v, self.add())
        return v

    def add(self) -> Any:
        v = self.mul()
        while self.peek() in ("+", "-"):
            op = self.take()
            w = self.mul()
            v = v + w if op == "+" else v - w
        return v

    def mul(self) -> Any:
        v = self.unary()
        while self.peek() in ("*", "/"):
            op = self.take()
            w = self.unary()
            v = v * w if op == "*" else int(v / w)
        return v

    def unary(self) -> Any:
        if self.peek() == "-":
            self.take()
            return -self.unary()
        if self.peek() == "!":
            self.take()
            return not self.unary()
        return self.primary()

    def primary(self) -> Any:
        tok = self.take()
        if tok == "(":
            v = self.expr()
            self.take(")")
            return v
        if tok.isdigit():
            return int(tok)
        low = tok.lower()
        if low in ("min", "max") and self.peek() == "(":
            self.take("(")
            args = [self.expr()]
            while self.peek() == ",":
                self.take()
                args.append(self.expr())
            self.take(")")
            return min(args) if low == "min" else max(args)
        if low in ("true", "false"):
            return low == "true"
        if self.peek() == "?" and self._is_nullable_marker():
            self.take("?")
        if self.peek() == "<" and _type_name(low) in _TYPE_NAMES:
            self.take("<")
            params = [self.param()]
            while self.peek() == ",":
                self.take()
                params.append(self.param())
            self.take(">")
            return Ty(_type_name(low), tuple(params))
        if tok in self.env:
            return self.env[tok]
        if low in self.env:
            return self.env[low]
        return Ty(_type_name(low))

    def _is_nullable_marker(self) -> bool:
        nxt = self.t[self.i + 1] if self.i + 1 < len(self.t) else None
        return nxt in (None, "<", ",", ">")

    def param(self) -> Any:
        # A parameter is a type or an integer expression.
        return self.add()


#: The YAMLs' type names that take parameters or stand alone.
_TYPE_NAMES = frozenset(_JSON_TO_YAML.values()) | {"timestamp", "timestamp_tz", "time"}


def _type_name(low: str) -> str:
    return {"bool": "boolean", "str": "string", "dec": "decimal"}.get(low, low)


def _strip_nullable(s: str) -> str:
    return re.sub(r"\?(?=<|$|,|>)", "", s.strip())


def _parse_type(s: str) -> Any:
    return _Expr(_strip_nullable(s), {}).expr()


def _match(decl: Any, actual: Ty, env: dict[str, Any]) -> bool:
    """Does `actual` match the declared type `decl`, binding its variables?"""
    if isinstance(decl, Ty) and decl.name.startswith("any") and not decl.params:
        key = decl.name
        if key in env:
            return env[key] == actual
        env[key] = actual
        return True
    if isinstance(decl, Ty) and decl.name.startswith("u!"):
        return False
    if not isinstance(decl, Ty) or decl.name != actual.name:
        # A type variable of a parameter: matched below.
        return False
    if not decl.params:
        return True
    if len(decl.params) != len(actual.params):
        return False
    for d, a in zip(decl.params, actual.params, strict=True):
        if isinstance(d, Ty) and isinstance(a, Ty):
            if not _match(d, a, env):
                return False
        elif isinstance(d, Ty) and not d.params and isinstance(a, int):
            # A variable such as P1.
            if d.name in env and env[d.name] != a:
                return False
            env[d.name] = a
        elif isinstance(d, int):
            if d != a:
                return False
        else:
            return False
    return True


def _decl(arg_type: str) -> Any:
    # Variables keep their spelling: `P1` must not become a type `p1`.
    return _Expr(_strip_nullable(arg_type), _Vars()).expr()


class _Vars(dict):
    """An environment that reads every identifier that names no type as a
    type variable, so that `decimal<P1,S1>` keeps `P1` and `S1` as names to
    bind."""

    def __contains__(self, key: object) -> bool:
        return isinstance(key, str) and _type_name(key.lower()) not in _TYPE_NAMES

    def __getitem__(self, key: str) -> Any:
        return Ty(key)


def _return(impl: Json, env: Mapping[str, Any]) -> Ty:
    """The impl's return type, its derivation evaluated with `env`."""
    lines = [ln.strip() for ln in impl["return"].splitlines() if ln.strip()]
    scope: dict[str, Any] = dict(env)
    for ln in lines[:-1]:
        name, _, rhs = ln.partition("=")
        scope[name.strip()] = _Expr(rhs, scope).expr()
    out = _Expr(_strip_nullable(lines[-1]), scope).expr()
    if not isinstance(out, Ty):
        raise ExportError(f"the return type {impl['return']!r} is not a type")
    return _close(out, scope)


def _close(t: Ty, env: Mapping[str, Any]) -> Ty:
    if t.name.startswith("any") and not t.params:
        bound = env.get(t.name)
        if not isinstance(bound, Ty):
            raise ExportError(f"the return type {t.name} is not bound")
        return bound
    params = []
    for p in t.params:
        if isinstance(p, Ty) and not p.params and p.name in env and isinstance(env[p.name], int):
            params.append(env[p.name])
        elif isinstance(p, Ty) and not p.params and p.name.upper() in env:
            params.append(env[p.name.upper()])
        elif isinstance(p, Ty):
            params.append(_close(p, env))
        else:
            params.append(p)
    return Ty(t.name, tuple(params))


def _short(arg: Json) -> str:
    if "enum" in arg:
        return "req"
    decl = _parse_type(arg["type"])
    name = decl.name if isinstance(decl, Ty) else str(decl)
    if name.startswith("any"):
        return "any"
    if name.startswith("u!"):
        return name
    return _SHORT.get(name, name)


@dataclasses.dataclass(frozen=True)
class Resolved:
    """A call's impl: its URN, compound name, output type and options."""

    urn: str
    compound: str
    output: Ty
    options: Mapping[str, Sequence[str]]


def resolve(name: str, kinds: Sequence[str], args: Sequence[Ty | str]) -> Resolved:
    """The YAML impl of `name` for these argument types (`str`: an enum
    argument's value)."""
    impls = [i for i in _extensions().get(name, []) if i["kind"] in kinds]
    # `count` and friends of `functions_aggregate_decimal_output` return a
    # decimal: the generic YAML's come first.
    impls.sort(key=lambda i: i["urn"].endswith("decimal_output"))
    if not impls:
        gap = FUNCTION_GAPS.get(name)
        raise ExportError(
            f"{name} is not a function of Substrait's YAMLs"
            + (f" ({gap})" if gap else "")
            + ": a conforming consumer would not know it"
        )
    for impl in impls:
        decls = impl["args"]
        variadic = impl.get("variadic")
        if variadic is None and len(decls) != len(args):
            continue
        if variadic is not None and (not decls or len(args) < max(variadic, len(decls) - 1)):
            continue
        env: dict[str, Any] = {}
        ok = True
        for k, a in enumerate(args):
            d = decls[min(k, len(decls) - 1)]
            if "enum" in d:
                ok = isinstance(a, str) and a in d["enum"]
            else:
                ok = isinstance(a, Ty) and _match(_decl(d["type"]), a, env)
            if not ok:
                break
        if not ok:
            continue
        compound = f"{name}:{'_'.join(_short(d) for d in decls)}" if decls else name
        return Resolved(impl["urn"], compound, _return(impl, env), impl.get("options") or {})
    shown = ", ".join(a if isinstance(a, str) else _show(a) for a in args)
    raise ExportError(f"no impl of {name} in Substrait's YAMLs takes ({shown})")


def _show(t: Ty) -> str:
    if not t.params:
        return t.name
    return f"{t.name}<{', '.join(_show(p) if isinstance(p, Ty) else str(p) for p in t.params)}>"


# -- the plan: types, URNs, compound names ------------------------------------


@dataclasses.dataclass
class Call:
    """A function call of the exported plan, as `_Typer` found it."""

    node: Json
    """The call's JSON (scalarFunction, measure, windowFunction), edited in place."""
    name: str
    resolved: Resolved
    args: tuple[Ty | str, ...]
    holder: Json | None = None
    """The expression the call is (`{"scalarFunction": node}`); None for
    measures and window functions."""


@dataclasses.dataclass
class Agg:
    """An aggregate relation of the plan, as `_Typer` found it."""

    container: Json
    """The relation (`{"aggregate": body}`), edited in place by shims."""
    body: Json
    key_types: list[Ty]


#: The anchors `_canonical` declares `is_nan` and `add` under, before the
#: anchors are renumbered.
_IS_NAN, _ADD = -1, -2

#: The written plan's operations whose double result may be `-0.0` or a
#: negative NaN under IEEE arithmetic (the writer's `.fadd`, `.fneg`,
#: `.fmath` and the rest, `Functions.lean`).
_DOUBLE_OPS = frozenset(
    {
        "add", "subtract", "multiply", "divide", "sverify_fmod", "power", "atan2", "logb",
        "negate", "floor", "ceil", "round", "sqrt", "exp", "ln", "log10", "log2", "sin",
        "cos", "tan", "asin", "acos", "atan",
    }
)  # fmt: skip
_FP64 = Ty("fp64")
#: Marks a call `_canonical` wrote or wrapped, which it leaves as it is.
_DONE = "__sverify_canonical"


class _Typer:
    """Types every expression of a written plan, and rewrites each call to
    name its impl: a new anchor per URN and compound name, and its output
    type."""

    def __init__(self, plan: Json):
        self.plan = plan
        self.names = {
            e["extensionFunction"]["functionAnchor"]: e["extensionFunction"]["name"]
            for e in plan.get("extensions", [])
            if "extensionFunction" in e
        }
        self.anchors: dict[tuple[str, str], int] = {}
        self.calls: list[Call] = []
        self.canonical = False
        """Whether the plan canonicalises doubles (`_canonical`)."""
        self.wrap = True
        """Whether to canonicalise doubles; off while `_peek` types a copy."""
        self.aggregates: list[Agg] = []
        self.sorts: list[tuple[Json, Ty]] = []
        self.casts: list[tuple[Json, Ty]] = []

    def anchor(self, r: Resolved) -> int:
        key = (r.urn, r.compound)
        if key not in self.anchors:
            self.anchors[key] = len(self.anchors) + 1
        return self.anchors[key]

    # relations

    def rel(self, r: Json) -> list[Ty]:
        if len(r) != 1:
            raise ExportError(f"cannot read the relation {sorted(r)}")
        [(kind, body)] = r.items()
        out = self._rel(kind, body)
        if kind == "aggregate":
            self.aggregates.append(Agg(r, body, self._keys))
        emit = (body.get("common") or {}).get("emit")
        if emit is not None:
            out = [out[i] for i in emit.get("outputMapping", [])]
        return out

    def _rel(self, kind: str, b: Json) -> list[Ty]:
        if kind == "read":
            return [ty_of(t) for t in b["baseSchema"]["struct"].get("types", [])] + self._exprs(
                b, [ty_of(t) for t in b["baseSchema"]["struct"].get("types", [])]
            )
        if kind in ("filter", "fetch", "sort"):
            cols = self.rel(b["input"])
            if kind == "filter":
                self.expr(b["condition"], cols)
            if kind == "fetch":
                for k in ("offsetExpr", "countExpr"):
                    if k in b:
                        self.expr(b[k], cols)
            for s in b.get("sorts", []):
                self._sort(s, cols)
            return cols
        if kind == "project":
            cols = self.rel(b["input"])
            return cols + [self.expr(e, cols) for e in b.get("expressions", [])]
        if kind == "aggregate":
            cols = self.rel(b["input"])
            keys = [self.expr(e, cols) for e in b.get("groupingExpressions", [])]
            for g in b.get("groupings", []):
                for e in g.get("groupingExpressions", []):
                    keys.append(self.expr(e, cols))
            ms = [self.measure(m, cols) for m in b.get("measures", [])]
            self._keys = keys
            order = []
            for g in b.get("groupings", []):
                for k in g.get("expressionReferences", []):
                    if int(k) not in order:
                        order.append(int(k))
            if b.get("groupingExpressions"):
                keys = [keys[k] for k in order]
            return keys + ms
        if kind in ("join", "cross"):
            left, right = self.rel(b["left"]), self.rel(b["right"])
            cols = left + right
            for k in ("expression", "postJoinFilter"):
                if k in b:
                    self.expr(b[k], cols)
            if b.get("type") in (
                "JOIN_TYPE_LEFT_SEMI",
                "JOIN_TYPE_LEFT_ANTI",
                "JOIN_TYPE_SEMI",
                "JOIN_TYPE_ANTI",
            ):
                return left
            return cols
        if kind == "set":
            outs = [self.rel(i) for i in b["inputs"]]
            return outs[0]
        raise ExportError(
            f"the plan has a {kind} relation, which to_substrait does not write for "
            "other consumers yet"
        )

    def _exprs(self, b: Json, cols: list[Ty]) -> list[Ty]:
        if "filter" in b:
            self.expr(b["filter"], cols)
        vt = b.get("virtualTable")
        if vt:
            for row in vt.get("expressions", []):
                for f in row.get("fields", []):
                    self.expr(f, cols)
        return []

    def _sort(self, s: Json, cols: list[Ty]) -> None:
        if (
            s.get("direction", "SORT_DIRECTION_UNSPECIFIED") == "SORT_DIRECTION_UNSPECIFIED"
            and "comparisonFunctionReference" not in s
        ):
            # ST-7: an unspecified direction leaves the NULL order open.
            raise ExportError(
                "a sort key has no direction (ST-7): Substrait leaves its NULL order open"
            )
        self.sorts.append((s, self.expr(s["expr"], cols)))

    # expressions

    def expr(self, e: Json, cols: list[Ty]) -> Ty:
        if "selection" in e:
            sel = e["selection"]
            if "rootReference" not in sel and "expression" not in sel:
                raise ExportError("to_substrait does not write outer references yet")
            t: Ty = (
                self.expr(sel["expression"], cols)
                if "expression" in sel
                else Ty("struct", tuple(cols))
            )
            ref = sel.get("directReference")
            while ref:
                if "structField" in ref:
                    sf = ref["structField"]
                    t = t.params[int(sf.get("field", 0))]
                    ref = sf.get("child")
                elif "listElement" in ref:
                    t = t.params[0]
                    ref = ref["listElement"].get("child")
                else:
                    raise ExportError(f"cannot read the reference {sorted(ref)}")
            return t
        if "literal" in e:
            return _literal(e["literal"])
        if "cast" in e:
            self.casts.append((e["cast"], self.expr(e["cast"]["input"], cols)))
            if (
                e["cast"].get("failureBehavior", "FAILURE_BEHAVIOR_UNSPECIFIED")
                == "FAILURE_BEHAVIOR_UNSPECIFIED"
            ):
                # ST-6: the reference throws (the parser's default).
                e["cast"]["failureBehavior"] = "FAILURE_BEHAVIOR_THROW_EXCEPTION"
            return ty_of(e["cast"]["type"])
        if "scalarFunction" in e:
            f = e["scalarFunction"]
            name = self.names.get(f.get("functionReference", 0), "")
            if (
                not f.pop(_DONE, False)
                and self.wrap
                and name.split(":")[0] in _DOUBLE_OPS
                and self._peek(e, cols) == _FP64
            ):
                self._canonical(e)
                return self.expr(e, cols)
            return self.call(f, cols, ("scalar",), holder=e)
        if "windowFunction" in e:
            w = e["windowFunction"]
            for p in w.get("partitions", []):
                self.expr(p, cols)
            for s in w.get("sorts", []):
                self._sort(s, cols)
            return self.call(w, cols, ("window", "aggregate"))
        if "ifThen" in e:
            it = e["ifThen"]
            outs = []
            for c in it.get("ifs", []):
                self.expr(c["if"], cols)
                outs.append(self.expr(c["then"], cols))
            if "else" in it:
                outs.append(self.expr(it["else"], cols))
            return outs[0]
        if "singularOrList" in e:
            s = e["singularOrList"]
            self.expr(s["value"], cols)
            for o in s.get("options", []):
                self.expr(o, cols)
            return Ty("boolean")
        if "nested" in e:
            n = e["nested"]
            if "list" in n:
                ts = [self.expr(v, cols) for v in n["list"].get("values", [])]
                return Ty("list", (ts[0],))
            if "struct" in n:
                return Ty(
                    "struct", tuple(self.expr(v, cols) for v in n["struct"].get("fields", []))
                )
        raise ExportError(
            f"to_substrait does not write {sorted(e)[0]} expressions for other consumers yet"
        )

    def _peek(self, e: Json, cols: list[Ty]) -> Ty:
        """The type of `e`, from a copy typed apart: `e` and this typer stay
        as they were."""
        t = copy.copy(self)
        t.names, t.anchors = dict(self.names), dict(self.anchors)
        t.calls, t.aggregates, t.sorts, t.casts = [], [], [], []
        t.wrap = False
        return t.expr(copy.deepcopy(e), cols)

    def _canonical(self, e: Json) -> None:
        """A double operation `x` as the reference has its result, with one
        zero and one NaN (ST-4): `y = x + 0.0` has no `-0.0`, and
        `if is_nan(y) then NaN else y` makes every NaN the positive one."""
        fp64 = {"literal": {"fp64": 0.0}}
        nan = {"literal": {"fp64": "NaN"}}

        orig = copy.deepcopy(e)

        def y() -> Json:
            x = copy.deepcopy(orig)
            x["scalarFunction"][_DONE] = True
            args = [{"value": x}, {"value": fp64}]
            return {"scalarFunction": {"functionReference": _ADD, "arguments": args, _DONE: True}}

        self.names[_IS_NAN], self.names[_ADD] = "is_nan", "add"
        test = {"scalarFunction": {"functionReference": _IS_NAN, "arguments": [{"value": y()}]}}
        e.clear()
        e["ifThen"] = {"ifs": [{"if": test, "then": nan}], "else": y()}
        self.canonical = True

    def measure(self, m: Json, cols: list[Ty]) -> Ty:
        if "filter" in m:
            self.expr(m["filter"], cols)
        f = m["measure"]
        for s in f.get("sorts", []):
            self._sort(s, cols)
        return self.call(f, cols, ("aggregate",))

    def call(self, f: Json, cols: list[Ty], kinds: Sequence[str], holder: Json | None = None) -> Ty:
        name = self.names.get(f.get("functionReference", 0))
        if name is None:
            raise ExportError(f"the plan calls an undeclared function {f.get('functionReference')}")
        base = name.split(":")[0]
        base = ALIASES.get(base, base)
        if base in FUNCTION_GAPS:
            raise ExportError(
                f"{base} maps non-ASCII text by a rule Substrait leaves open "
                f"({FUNCTION_GAPS[base]}, upstream/bugs/{FUNCTION_GAPS[base]}.json)"
            )
        args: list[Ty | str] = []
        for a in f.get("arguments", []):
            if "value" in a:
                args.append(self.expr(a["value"], cols))
            elif "enum" in a:
                args.append(a["enum"])
            elif "type" in a:
                args.append(ty_of(a["type"]))
            else:
                raise ExportError(f"cannot read an argument of {base}")
        if base in _COMPARISONS and len(args) == 2 and args[0] != args[1]:
            args = self._unify(f, args)
        if base in ("shift_left", "shift_right") and len(args) == 2 and args[1] == Ty("i64"):
            # The YAML's count is an `i32`. The cast raises only on counts
            # outside `[0, 63]`, where the reference raises (ST-1).
            arg = f["arguments"][1]
            arg["value"] = _cast(arg["value"], Ty("i32"))
            args[1] = Ty("i32")
        r = resolve(base, kinds, args)
        f["functionReference"] = self.anchor(r)
        f["outputType"] = r.output.json()
        self.calls.append(Call(f, base, r, tuple(args), holder))
        return r.output

    def _unify(self, f: Json, args: list[Ty | str]) -> list[Ty | str]:
        """A comparison's arguments cast to a common type where the writer
        relies on the consumer's coercion (a decimal against an integer, two
        integer widths): each cast widens exactly."""
        a, b = args
        if not (isinstance(a, Ty) and isinstance(b, Ty)):
            return args
        common = _common(a, b)
        if common is None:
            return args
        for k, t in enumerate((a, b)):
            if t != common:
                arg = f["arguments"][k]
                arg["value"] = _cast(arg["value"], common)
        return [common, common]

    def run(self) -> None:
        for rel in self.plan.get("relations", []):
            root = rel.get("root") or {}
            self.rel(root.get("input") or rel.get("rel"))
        urns = sorted({u for u, _ in self.anchors})
        anchor_of = {u: k + 1 for k, u in enumerate(urns)}
        self.plan["extensionUrns"] = [{"extensionUrnAnchor": anchor_of[u], "urn": u} for u in urns]
        self.plan["extensions"] = [
            {
                "extensionFunction": {
                    "extensionUrnReference": anchor_of[u],
                    "functionAnchor": a,
                    "name": c,
                }
            }
            for (u, c), a in sorted(self.anchors.items(), key=lambda kv: kv[1])
        ]


_COMPARISONS = frozenset(
    {"equal", "not_equal", "lt", "gt", "lte", "gte", "is_distinct_from", "is_not_distinct_from"}
)
_INT_DIGITS = {"i8": 3, "i16": 5, "i32": 10, "i64": 19}
_INT_ORDER = ("i8", "i16", "i32", "i64")


def _common(a: Ty, b: Ty) -> Ty | None:
    """The type both widen to exactly, if there is one."""
    if a.name in _INT_DIGITS and b.name in _INT_DIGITS:
        return max(a, b, key=lambda t: _INT_ORDER.index(t.name))
    if {a.name, b.name} <= {"decimal", *_INT_DIGITS}:

        def ps(t: Ty) -> tuple[int, int]:
            return (t.params[0], t.params[1]) if t.name == "decimal" else (_INT_DIGITS[t.name], 0)

        (p1, s1), (p2, s2) = ps(a), ps(b)
        scale = max(s1, s2)
        prec = max(p1 - s1, p2 - s2) + scale
        if prec > 38:
            return None
        return Ty("decimal", (prec, scale))
    return None


def _cast(e: Json, t: Ty) -> Json:
    return {
        "cast": {
            "type": t.json(),
            "input": e,
            "failureBehavior": "FAILURE_BEHAVIOR_THROW_EXCEPTION",
        }
    }


def _literal(lit: Json) -> Ty:
    keys = [k for k in lit if k not in ("nullable", "typeVariationReference")]
    if not keys:
        raise ExportError("a literal without a value")
    k = keys[0]
    v = lit[k]
    simple = {
        "boolean": "boolean",
        "i8": "i8",
        "i16": "i16",
        "i32": "i32",
        "i64": "i64",
        "fp32": "fp32",
        "fp64": "fp64",
        "string": "string",
        "binary": "binary",
        "date": "date",
        "intervalYearToMonth": "interval_year",
        "uuid": "uuid",
    }
    if k in simple:
        return Ty(simple[k])
    if k == "decimal":
        return Ty("decimal", (int(v.get("precision", 0)), int(v.get("scale", 0))))
    if k in ("precisionTimestamp", "precisionTimestampTz", "precisionTime"):
        name = {
            "precisionTimestamp": "precision_timestamp",
            "precisionTimestampTz": "precision_timestamp_tz",
            "precisionTime": "precision_time",
        }[k]
        return Ty(name, (int(v.get("precision", 6)),))
    if k == "intervalDayToSecond":
        return Ty("interval_day", (int(v.get("precision", 6)),))
    if k == "intervalCompound":
        return Ty("interval_compound")
    if k == "null":
        return ty_of(v)
    if k == "emptyList":
        return Ty("list", (ty_of(v["type"]),))
    if k == "list":
        return Ty("list", (_literal(v["values"][0]),))
    if k == "struct":
        return Ty("struct", tuple(_literal(f) for f in v.get("fields", [])))
    if k in ("varChar", "fixedChar"):
        return Ty("string")
    raise ExportError(f"to_substrait cannot type the literal {k}")


# -- the options --------------------------------------------------------------


def _groups(call: Call) -> set[str]:
    """The function groups of `Functions.lean` a call belongs to, from its
    name and the kind of its arguments."""
    from sverify import routes

    rows = [r for r in routes._functions_json() if r.get("name") == call.name and r.get("group")]
    tys = [a for a in call.args if isinstance(a, Ty)]
    names = {t.name for t in tys}
    fp = bool(names & {"fp32", "fp64"})
    prefix = (
        "fp."
        if fp
        else "dec."
        if "decimal" in names
        else "time."
        if names
        & {
            "date",
            "precision_timestamp",
            "precision_timestamp_tz",
            "interval_day",
            "interval_year",
            "precision_time",
        }
        else "int."
        if names & {"i8", "i16", "i32", "i64"}
        else None
    )
    if call.name == "avg" and "decimal" not in names:
        # `parseMeasure` reads `avg`'s options as of doubles.
        return {r["group"] for r in rows if r["group"] == "agg.fsum"} or {r["group"] for r in rows}
    narrowed = [r for r in rows if (r.get("reads") == "float") == fp]
    rows = narrowed or rows
    if call.resolved and call.name in _AGG_NAMES and len(rows) > 1:
        mark = ".f" if fp else ".d" if "decimal" in names else ".i"
        rows = [r for r in rows if mark in r["group"]] or rows
    if prefix is not None and any(r["group"].startswith(prefix) for r in rows):
        rows = [r for r in rows if r["group"].startswith(prefix)]
    return {r["group"] for r in rows}


_AGG_NAMES = frozenset({"sum", "sum0", "min", "max"})


def _yaml_names() -> dict[str, str | None]:
    """sverify's option ids, each with its name in Substrait's YAMLs (None:
    sverify's own)."""
    from sverify import routes

    return {o["id"]: o.get("substrait") for o in routes._options_json().get("options", [])}


@dataclasses.dataclass
class Handling:
    """What the export did at the options the proof depends on."""

    pinned: list[Json] = dataclasses.field(default_factory=list)
    unexercised: list[Json] = dataclasses.field(default_factory=list)
    up_to: list[Json] = dataclasses.field(default_factory=list)
    shims: list[Json] = dataclasses.field(default_factory=list)
    assumptions: list[Json] = dataclasses.field(default_factory=list)


def _dependencies(plan_json: str) -> list[Json]:
    from sverify.engine import run_checker

    code, out, err = run_checker(("--dependencies",), plan_json)
    if code != 0:
        raise ExportError(f"substrait-check --dependencies failed: {(err or out).strip()}")
    return json.loads(out).get("options", [])


def _pin(report: Report, typer: _Typer, shims: Shims) -> Handling:
    """Pin every option the proof depends on, and account for the rest."""
    from sverify import _substrait_shims, routes
    from sverify.report import INFINITE

    assert report.internal_plan is not None
    calls = typer.calls
    canonical = typer.canonical
    builder = _substrait_shims.Builder(typer.plan)
    applied_by: dict[Any, Json | None] = {}

    def run_shim(o: str) -> Json | None:
        fn = _substrait_shims.SHIMS.get(o)
        if fn is None:
            return None
        if fn not in applied_by:
            applied_by[fn] = fn(typer, builder)
        return applied_by[fn]

    h = Handling()
    reads = _dependencies(report.internal_plan)
    used = (
        {(d.get("group"), d["option"]) for d in report._depends}
        if report._depends is not None
        else {(r["group"], r["option"]) for r in reads}
    )
    yaml_name = _yaml_names()
    by_key: dict[tuple[str, str], list[Json]] = {}
    for r in reads:
        if (r["group"], r["option"]) in used or (None, r["option"]) in used:
            by_key.setdefault((r["group"], r["option"]), []).append(r)
    rows = []
    for (g, o), rs in by_key.items():
        ref = list(dict.fromkeys(b for r in rs for b in r["reference"]["allows"]))
        sub = rs[0]["substrait"]["choice"] or {}
        prefs: list[str] = []
        yname = yaml_name.get(o)
        if sub.get("kind") == "asked" and yname is not None:
            values = sub.get("behaviours") or []
            prefs = [b for b in ref if b in values]
            if rs[0].get("tool") == "raise" and "ERROR" in prefs:
                # Where the reference raises, the consumer raises first.
                prefs = ["ERROR", *(b for b in prefs if b != "ERROR")]
            targets = [c for c in calls if g in _groups(c)]
            if prefs and targets and all(yname in c.resolved.options for c in targets):
                for c in targets:
                    _set_option(c.node, yname, prefs)
                h.pinned.append(
                    {
                        "group": g,
                        "option": o,
                        "yaml_option": yname,
                        "values": prefs,
                        "functions": sorted({c.resolved.compound for c in targets}),
                    }
                )
            else:
                prefs = []
        rows.append(
            {
                "group": g,
                "option": o,
                "behaviours": ref,
                "preferences": prefs or sorted({p for r in rs for p in r.get("preferences", [])}),
                "tool": rs[0].get("tool"),
            }
        )
    result = routes.lean_transfer(
        "reference",
        "substrait",
        [{k: r[k] for k in ("group", "option", "behaviours", "preferences")} for r in rows],
    )
    if result is None:
        raise ExportError("this checker has no transfer check (substrait-check --transfer)")
    tool = {(r["group"], r["option"]): r["tool"] for r in rows}
    assumed_options = set()
    for i in report.assumed:
        assumed_options.add("float_overflow" if i.kind == INFINITE else "overflow")
    problems = []
    for f in result["failures"]:
        if "function" in f:
            problems.append(f"{f['function']} has no Substrait form")
            continue
        g, o = f.get("group"), f["option"]
        gap = GAPS.get(o)
        where = f"{g}'s {o}" if g else o
        r = routes.row("substrait", g, o) or {}
        uses = f.get("from") or []
        if (
            o in ("zero_sign", "nan_kind")
            and canonical
            and g not in ("rel.keys", "rel.sort", "cmp")
        ):
            # The exported plan canonicalises each double an operation gives
            # (`_Typer._canonical`): one zero and one NaN, as the reference
            # has.
            _note(
                h.shims,
                {
                    "option": "zero_sign/nan_kind",
                    "gap": "ST-4",
                    "shim": "x + 0.0, then if is_nan(y) then NaN else y, after each "
                    "double operation that can give -0.0 or a NaN",
                    "source": "written plan",
                },
            )
            continue
        if tool.get((g, o)) == "leave_open":
            # The reference leaves the choice open too: the proof covers
            # every behaviour, Substrait's among them.
            h.unexercised.append(
                {"group": g, "option": o, "why": "the reference leaves it open as well"}
            )
            continue
        if (
            o == "rounding"
            and list(uses) == ["TIE_TO_EVEN"]
            and (g or "").startswith(("fp.", "agg.f"))
        ):
            # A double operation whose YAML has no `rounding` option: fp64 is
            # IEEE 754's (`type_classes.md`), whose default rounding is ties
            # to even (ST-9).
            h.up_to.append(
                {
                    "group": g,
                    "option": o,
                    "gap": "ST-9",
                    "equivalence": {},
                    "why": "IEEE 754's default rounding, which fp64 follows; tested, "
                    "not stated by the YAML",
                }
            )
            continue
        if tool.get((g, o)) == "raise":
            # The reference raises there, and the plan is proved not to on
            # inputs that meet the preconditions, which the export ships: a
            # consumer never meets the choice. An assumed issue at the option
            # is a precondition too (`Report.assumed`, shipped as "assumed").
            h.unexercised.append(
                {
                    "group": g,
                    "option": o,
                    **({"gap": gap} if gap else {}),
                    "why": "the reference raises there, and the preconditions rule those inputs out"
                    + ("; an assumed precondition covers it" if o in assumed_options else ""),
                }
            )
            continue
        if o == "decimal_rescale" and (done := run_shim(o)) is not None:
            # No rewrite: the plan never rescales (every mode).
            h.unexercised.append({"group": g, "option": o, "gap": gap, "why": done["shim"]})
            continue
        observed = None
        if r.get("class") in ("refines_up_to", "approx") and r.get("q") is not None:
            from sverify.observation import from_json

            q = from_json(r["q"])
            missed = q.coarser_than(report.observation)
            if not missed:
                h.up_to.append({"group": g, "option": o, "equivalence": r["q"]})
                continue
            if missed == ["floats"] and q.floats == "plan" and (met := _plan_bound_met(report)):
                # D25: the consumer adds in its own order, within the plan's
                # proved bound, which meets the postconditions' tolerance.
                h.up_to.append({"group": g, "option": o, "equivalence": {"floats": met}})
                continue
            observed = (
                f"{where}: a Substrait consumer agrees with the reference only up to {q}, "
                f"and the postconditions observe its {', '.join(missed)} ({report.observation}); "
                f"state {', '.join(missed)} in sv.equivalent(...)"
            )
        if shims == "annotate":
            h.assumptions.append(
                {
                    "group": g,
                    "option": o,
                    **({"gap": gap} if gap else {}),
                    "assumes": uses,
                    "text": f"the consumer gives {', '.join(uses)} at {where}",
                }
            )
            continue
        if shims == "apply" and (done := run_shim(o)) is not None:
            h.shims.append({"group": g, "option": o, **({"gap": gap} if gap else {}), **done})
            continue
        if observed is not None:
            problems.append(observed)
            continue
        problems.append(
            f"{where}: Substrait allows {', '.join(f.get('to') or ['any behaviour'])} where the "
            f"proof uses {', '.join(uses)}"
            + (f" ({gap}, upstream/bugs/{gap}.json)" if gap else "")
            + (
                "; no shim writes it for this plan: export with shims='annotate' to ship it "
                "as an assumption"
                if shims == "apply"
                else "; export with shims='apply' or 'annotate'"
                if shims == "refuse"
                else ""
            )
        )
    if problems:
        raise ExportError("refused for Substrait: " + "; ".join(problems))
    return h


def _note(rows: list[Json], row: Json) -> None:
    if row not in rows:
        rows.append(row)


def _set_option(f: Json, name: str, prefs: Sequence[str]) -> None:
    opts = f.setdefault("options", [])
    for o in opts:
        if o.get("name") == name:
            # A preference the plan states (Lean wrote it) stays first.
            o["preference"] = list(dict.fromkeys([*o.get("preference", []), *prefs]))
            return
    opts.append({"name": name, "preference": list(prefs)})


# -- the contract message -----------------------------------------------------


@functools.cache
def _messages() -> tuple[type, type]:
    """`Contract` and `Condition` (`contract.proto`), built in the default
    descriptor pool next to Substrait's own messages."""
    from google.protobuf import descriptor_pb2, descriptor_pool, message_factory, struct_pb2
    from substrait import plan_pb2

    pool = descriptor_pool.Default()
    name = f"{PACKAGE}.Contract"
    try:
        pool.FindMessageTypeByName(name)
    except KeyError:
        F = descriptor_pb2.FieldDescriptorProto
        fdp = descriptor_pb2.FileDescriptorProto(
            name="io/sverify/substrait/v1/contract.proto",
            package=PACKAGE,
            syntax="proto3",
            dependency=[plan_pb2.DESCRIPTOR.name, struct_pb2.DESCRIPTOR.name],
        )

        def field(msg, n, num, typ, label=F.LABEL_OPTIONAL, type_name=None):
            f = msg.field.add(name=n, number=num, type=typ, label=label)
            if type_name:
                f.type_name = type_name

        c = fdp.message_type.add(name="Contract")
        field(c, "manifest", 1, F.TYPE_MESSAGE, type_name=".google.protobuf.Struct")
        field(c, "requires", 2, F.TYPE_MESSAGE, F.LABEL_REPEATED, f".{PACKAGE}.Condition")
        field(c, "ensures", 3, F.TYPE_MESSAGE, F.LABEL_REPEATED, f".{PACKAGE}.Condition")
        d = fdp.message_type.add(name="Condition")
        field(d, "text", 1, F.TYPE_STRING)
        field(d, "table", 2, F.TYPE_STRING)
        field(d, "kind", 3, F.TYPE_STRING)
        field(d, "inferred", 4, F.TYPE_BOOL)
        field(d, "plan", 5, F.TYPE_MESSAGE, type_name=".substrait.Plan")
        field(d, "entry", 6, F.TYPE_MESSAGE, type_name=".google.protobuf.Value")
        field(d, "proved", 7, F.TYPE_BOOL)
        pool.Add(fdp)
    contract = message_factory.GetMessageClass(pool.FindMessageTypeByName(name))
    condition = message_factory.GetMessageClass(pool.FindMessageTypeByName(f"{PACKAGE}.Condition"))
    return contract, condition


def _plan_message(plan: Json) -> Any:
    from google.protobuf import json_format
    from substrait import plan_pb2

    try:
        return json_format.ParseDict(plan, plan_pb2.Plan())
    except json_format.ParseError as e:
        raise ExportError(f"the plan is not Substrait {_version()}: {e}") from e


def _plan_dict(msg: Any) -> Json:
    from google.protobuf import json_format

    return json_format.MessageToDict(msg)


def _version() -> str:
    return ".".join(map(str, SUBSTRAIT_VERSION))


def _sverify_version() -> str:
    return _meta.VERSION


def _table_condition_json(c: Any) -> Json:
    fields: dict[str, Any] = {}
    for f in dataclasses.fields(c):
        v = getattr(c, f.name)
        fields[f.name] = (
            v.total_seconds()
            if isinstance(v, timedelta)
            else list(v)
            if isinstance(v, tuple)
            else v
        )
    return {"class": type(c).__name__, "fields": fields}


def _table_condition(j: Mapping[str, Any]) -> Any:
    from sverify import conditions

    allowed = {"Unique", "References", "ArrivesWithin", "MaxRows", "RowsPer"}
    cls = j.get("class")
    if cls not in allowed:
        raise ValueError(f"unknown table condition {cls!r}")
    fields = dict(j.get("fields") or {})
    if cls == "ArrivesWithin":
        fields["lateness"] = timedelta(seconds=fields["lateness"])
    for k in ("cols",):
        if k in fields:
            fields[k] = tuple(fields[k])
    if "n" in fields:
        fields["n"] = int(fields["n"])
    return getattr(conditions, cls)(**fields)


def _condition(plan: Json, name: str | None = None) -> Json:
    """A condition's plan, as Lean writes it and with URNs, compound names
    and output types; a postcondition's column is named by its label."""
    from sverify.engine import written_plan

    out = _conform(json.loads(written_plan(json.dumps(plan))))
    if name is not None:
        out["relations"][0]["root"]["names"] = [name]
    return out


def _conform(plan: Json) -> Json:
    """`plan` with URNs, compound names and output types."""
    out = copy.deepcopy(plan)
    _Typer(out).run()
    return out


# -- the export ---------------------------------------------------------------


def export(report: Report, format: Format = "json", *, shims: Shims = "apply") -> str | bytes:
    """`Report.to_substrait`: see there."""
    _check_format(format)
    plan, contract = _export(report, shims)
    msg = _plan_message(plan)
    from google.protobuf import any_pb2, json_format

    packed = any_pb2.Any()
    packed.Pack(contract, type_url_prefix="type.googleapis.com/")
    msg.advanced_extensions.optimization.append(packed)
    if format == "binary":
        return msg.SerializeToString(deterministic=True)
    if format == "json":
        return json_format.MessageToJson(msg, sort_keys=True)
    raise ValueError(f"format must be 'json' or 'binary', not {format!r}")


def contract_json(report: Report, *, shims: Shims = "apply") -> Json:
    """`Report.substrait_contract`: the contract as JSON, for a sidecar."""
    from google.protobuf import json_format

    _, contract = _export(report, shims)
    return json_format.MessageToDict(contract)


def _refuse_unverified(report: Report) -> None:
    if report.internal_plan is None or report._contract is None:
        raise ExportError("this report has no plan to export: it was not made by sv.verify")
    if not report.proved:
        reasons = [f"not proved: {c.label}" for c in report.ensures if not c.portable]
        reasons += [f"may fail: {i}" for i in report.errors]
        if report._transfer:
            reasons.append("the proof does not carry over to Substrait (see str(report))")
        reasons += [f"needs {n}" for n in report._needs_lines()]
        if report.floats_unmet:
            reasons.append(f"no engine meets the observation's doubles: {report.floats_unmet}")
        raise ExportError("not verified: " + "; ".join(reasons))


def _export(report: Report, shims: Shims = "apply") -> tuple[Json, Any]:
    from sverify import routes
    from sverify.engine import written_plan

    if shims not in SHIMS:
        raise ValueError(f"shims must be one of {', '.join(map(repr, SHIMS))}, not {shims!r}")
    _refuse_unverified(report)
    assert report.internal_plan is not None and report._contract is not None
    plan = json.loads(written_plan(report.internal_plan))
    typer = _Typer(plan)
    typer.run()
    if report.semantics == "substrait":
        handling = Handling()
    elif report.semantics == "reference":
        handling = _pin(report, typer, shims)
        # Shims add calls: type the plan again, for their URNs and types.
        _Typer(plan).run()
    else:
        raise ExportError(
            f"a plan verified with semantics={report.semantics!r} holds on that engine only; "
            "verify it with semantics='reference' or 'substrait' to export it"
        )
    major, minor, patch = SUBSTRAIT_VERSION
    plan["version"] = {
        "majorNumber": major,
        "minorNumber": minor,
        "patchNumber": patch,
        "producer": f"sverify {_sverify_version()}",
    }
    contract_cls, condition_cls = _messages()
    from google.protobuf import struct_pb2

    c = contract_cls()
    requires_plans = iter(report._contract.get("requires", []))
    for table, conds in report._conditions.items():
        inferred = {str(x) for x in report._inferred.get(table, [])}
        for cond in conds:
            from sverify.conditions import TableCondition, label

            entry = condition_cls(
                table=table,
                text=label(cond),
                inferred=str(cond) in inferred and isinstance(cond, str),
            )
            if isinstance(cond, TableCondition):
                entry.kind = type(cond).__name__
                entry.entry.struct_value.update(_table_condition_json(cond))
            else:
                entry.kind = "row"
                entry.plan.CopyFrom(_plan_message(_condition(next(requires_plans))))
            c.requires.append(entry)
    for i in report.assumed:
        from sverify.report import _assumption

        c.requires.append(condition_cls(text=_assumption(i), kind="assumed", inferred=True))
    ens_plans = iter(report._contract.get("ensures", []))
    posts = report._postconditions or []
    if len(posts) != len(report.ensures):
        raise ExportError("this report keeps no postconditions to export (re-run sv.verify)")
    from sverify.conditions import TableCondition

    for cond, checked in zip(posts, report.ensures, strict=True):
        entry = condition_cls(text=checked.label, proved=checked.proved)
        if isinstance(cond, TableCondition):
            entry.kind = type(cond).__name__
            entry.entry.struct_value.update(_table_condition_json(cond))
        else:
            entry.kind = "row"
            entry.plan.CopyFrom(_plan_message(_condition(next(ens_plans), checked.label)))
        c.ensures.append(entry)
    observation = report.observation
    manifest: Json = {
        "format": FORMAT,
        "sverify": _sverify_version(),
        "substrait": _version(),
        "extension_urns": [u["urn"] for u in plan.get("extensionUrns", [])],
        "semantics": report.semantics,
        "class": "assumed"
        if handling.assumptions
        else "observed"
        if any(u.get("equivalence") for u in handling.up_to)
        or routes.plan_bound(report._epsilon) is not None
        else "exact",
        "evidence": "tested" if any(u.get("gap") == "ST-9" for u in handling.up_to) else "proved",
        "shims_mode": shims,
        "equivalence": str(observation),
        "equivalence_components": {
            k: (str(v) if not isinstance(v, str) else v)
            for k, v in dataclasses.asdict(observation).items()
            if k != "bound"
        },
        "pinned": handling.pinned,
        "unexercised": handling.unexercised,
        "up_to": handling.up_to,
        "shims": handling.shims,
        "assumptions": handling.assumptions,
        "deterministic": report.deterministic,
        "rows": report.rows,
        "params": list(report._params),
        "output": {k: str(v) for k, v in report.output.items()},
        "checker_contract": {
            k: report._contract[k]
            for k in ("keys", "ensures_keys", "references", "max_rows", "rows_per")
            if k in report._contract
        },
    }
    s = struct_pb2.Struct()
    s.update(json.loads(json.dumps(manifest)))
    c.manifest.CopyFrom(s)
    return plan, c


# -- the import ---------------------------------------------------------------


@dataclasses.dataclass(frozen=True)
class Imported:
    """A plan read back by `from_substrait`."""

    plan: Json
    """The plan, without the contract."""
    manifest: Json
    requires: list[Json]
    ensures: list[Json]


#: The manifest's keys that format 2 renamed (K1, K2).
_RENAMED = {
    "profile": "semantics",
    "observation": "equivalence",
    "observation_components": "equivalence_components",
}


def _manifest(m: Mapping[str, Any]) -> Json:
    """The manifest in this version's format: a format 1 manifest's keys
    renamed, `rows` an integer (a Struct holds every number as a double).

    Raises:
        ValueError: The manifest's format is newer than this version reads.
    """
    fmt = m.get("format", 1)
    if not isinstance(fmt, int | float) or fmt > FORMAT:
        raise ValueError(
            f"the plan's sverify contract has format {fmt!r}, and this version of sverify "
            f"reads format {FORMAT} or older: upgrade sverify"
        )
    out = dict(m)
    if fmt < 2:
        out = {_RENAMED.get(k, k): v for k, v in out.items()}
        out["up_to"] = [
            {("equivalence" if k == "observation" else k): v for k, v in u.items()}
            for u in out.get("up_to") or []
        ]
        out["format"] = FORMAT
    if isinstance(out.get("rows"), float) and out["rows"].is_integer():
        out["rows"] = int(out["rows"])
    if isinstance(out.get("format"), float):
        out["format"] = int(out["format"])
    return out


def read(data: str | bytes | Mapping[str, Any]) -> Imported:
    """The plan and its contract from an export (`to_substrait`'s output, in
    either format, or its JSON as a dict)."""
    from google.protobuf import json_format
    from substrait import plan_pb2

    contract_cls, _ = _messages()
    msg = plan_pb2.Plan()
    if isinstance(data, bytes):
        msg.ParseFromString(data)
    elif isinstance(data, str):
        json_format.Parse(data, msg)
    else:
        json_format.ParseDict(dict(data), msg)
    found = None
    rest = []
    for a in msg.advanced_extensions.optimization:
        if a.type_url == TYPE_URL:
            found = contract_cls()
            a.Unpack(found)
        else:
            rest.append(a)
    if found is None:
        raise ValueError(f"the plan carries no sverify contract ({TYPE_URL})")
    del msg.advanced_extensions.optimization[:]
    msg.advanced_extensions.optimization.extend(rest)
    if not rest and not msg.advanced_extensions.HasField("enhancement"):
        msg.ClearField("advanced_extensions")
    d = json_format.MessageToDict(found)
    return Imported(
        _plan_dict(msg),
        _manifest(d.get("manifest", {})),
        list(d.get("requires", [])),
        list(d.get("ensures", [])),
    )


def from_substrait(data: str | bytes | Mapping[str, Any]) -> Report:
    """Read a plan `Report.to_substrait` exported, and prove its contract
    again with the checker (#664).

    The plan goes to the checker as it was exported, pinned options, shims
    and all, with the preconditions and postconditions it carries; the
    report says what the checker proves of it now. For an export of a
    verified plan, `proved` is true again, with the same postconditions.

    Args:
        data: The export: protobuf JSON (a string or its dict) or bytes.

    Returns:
        A `Report` of the plan: its postconditions with their status, the
        runtime errors the checker cannot rule out, the facts on each output
        column and the options the proof depends on. Facts are in Lean's
        notation, and nothing is known of the Ibis types.

    Raises:
        ValueError: The plan carries no sverify contract, or the checker
            rejects the plan.
    """
    return recheck(data)


def _floats_component(components: Mapping[str, Any]) -> Any:
    """The `floats` of a manifest's observation: `"exact"`, `"plan"` (also
    where the manifest has none), or a tolerance, written as its fields."""
    import ast

    from sverify.observation import Within

    v = components.get("floats", "plan")
    if v in ("exact", "plan"):
        return v
    try:
        fields = ast.literal_eval(v)
        return Within(fields.get("abs"), fields.get("rel"), fields.get("ulps"))
    except (ValueError, SyntaxError, AttributeError, TypeError):
        return "plan"


def recheck(data: str | bytes | Mapping[str, Any]) -> Report:
    """`from_substrait`, under its internal name."""
    from sverify.conditions import CheckedCondition
    from sverify.engine import run_checker
    from sverify.observation import Observation
    from sverify.report import Issue, Report, tie_places

    imp = read(data)
    m = imp.manifest
    stored = m.get("checker_contract") or {}
    request: Json = {
        "requires": [_lean_plan(r["plan"]) for r in imp.requires if r.get("kind") == "row"],
        "ensures": [],
        "transform": _lean_plan(imp.plan),
        "keys": stored.get("keys", {}),
        "ensures_keys": stored.get("ensures_keys", []),
        "references": stored.get("references", {}),
        "max_rows": _ints(stored.get("max_rows", {})),
        "rows_per": stored.get("rows_per", {}),
    }
    for e in imp.ensures:
        if e.get("kind") == "row":
            p = _lean_plan(e["plan"])
            p["relations"][0]["root"]["names"] = [e["text"]]
            request["ensures"].append(p)
    request = json.loads(json.dumps(request), parse_float=_num)
    request["ensures_keys"] = [[int(x) for x in k] for k in request["ensures_keys"]]
    request["keys"] = {t: [[int(x) for x in k] for k in ks] for t, ks in request["keys"].items()}
    if m.get("semantics") == "substrait":
        request["profile"] = "substrait"
    code, stdout, stderr = run_checker(("--contract",), json.dumps(request))
    if code not in (0, 4):
        raise ValueError(f"substrait-check --contract failed on the import: {stderr.strip()}")
    out = json.loads(stdout)
    rows = iter(out["ensures"])
    keys = iter(out["keys"])

    def next_key() -> tuple[bool, None]:
        return next(keys)["proved"], None

    checked = []
    for e in imp.ensures:
        if e.get("kind") == "row":
            r = next(rows)
            checked.append(CheckedCondition(e["text"], r["proved"], r["value"]))
        else:
            checked.append(_table_condition(e["entry"]).ensured(out, next_key))
    requires: dict[str, list[str]] = {}
    for r in imp.requires:
        if r.get("table"):
            requires.setdefault(r["table"], []).append(r["text"])
    components = {
        k: v
        for k, v in (m.get("equivalence_components") or {}).items()
        if k not in ("floats", "bound")
    }
    observation = dataclasses.replace(
        Observation(floats=_floats_component(m.get("equivalence_components") or {})), **components
    )
    profile = m.get("semantics", "reference")
    return Report(
        semantics=profile,
        requires=requires,
        ensures=checked,
        facts={f["name"]: f["value"] for f in out["facts"]},
        deterministic=out["deterministic"],
        _windows_total=out.get("windows_total", out["deterministic"]),
        _tie_places=tie_places(out),
        issues=[
            Issue(i["kind"], i["expr"], i["error"], assumed=i.get("assumed", False))
            for i in out["issues"]
            if i["error"] and i["kind"] not in ("SUM overflow", "overflow to infinity")
        ],
        _guard_free=out["guard_free"],
        rows=out.get("rows"),
        internal_plan=json.dumps(imp.plan),
        _depends=out.get("depends"),
        _epsilon=out.get("epsilon"),
        _engines=out.get("engines"),
        _sorted=out.get("sorted"),
        _contract=request,
        _transfer=(out.get("transfer") or {}).get("failures") if profile == "substrait" else None,
        observation=observation,
        _params=list(m.get("params") or []),
    )


def _num(s: str) -> Any:
    f = float(s)
    return int(f) if f.is_integer() else f


def _ints(d: Mapping[str, Any]) -> dict[str, int]:
    return {k: int(v) for k, v in d.items()}


def _lean_plan(plan: Json) -> Json:
    """A plan as protobuf JSON for the checker, with the field 0 of a
    reference written out: protobuf's JSON leaves out zero values."""
    return _fill_defaults(copy.deepcopy(plan))


def _fill_defaults(node: Any) -> Any:
    if isinstance(node, dict):
        if isinstance(node.get("structField"), dict):
            node["structField"].setdefault("field", 0)
        for v in node.values():
            _fill_defaults(v)
    elif isinstance(node, list):
        for v in node:
            _fill_defaults(v)
    return node


def _check_format(format: str) -> None:
    if format not in ("json", "binary"):
        raise ValueError(f"format must be 'json' or 'binary', not {format!r}")


__all__ = [
    "FORMAT",
    "GAPS",
    "TYPE_URL",
    "ExportError",
    "Imported",
    "contract_json",
    "export",
    "from_substrait",
    "read",
    "recheck",
    "resolve",
]


def _plan_bound_met(report: Any) -> dict[str, float] | None:
    """The plan's proved bound on its doubles (`Report.epsilon`) as a
    tolerance, when it meets the one the postconditions state on every
    double column; None otherwise."""
    from sverify.observation import Within
    from sverify.routes import _bounds

    floats = report.observation.floats
    if not isinstance(floats, Within) or not report._epsilon:
        return None
    met: dict[str, float] = {}
    for eps in report._epsilon.values():
        ok = False
        for kind, (v, proved) in _bounds(eps).items():
            tol = getattr(floats, kind)
            if tol is not None and proved and v <= tol:
                ok = True
                met[kind] = max(met.get(kind, 0.0), v)
        if not ok:
            return None
    return met or None

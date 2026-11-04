"""Run Substrait's own function test cases against `Profile.substrait` (#444, step 4).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

`substrait-io/substrait` keeps test cases for its extension functions in
`tests/cases/<area>/*.test` (the format is its `tests/README.md`): a call, the
options it states, and the expected result, an error (`<!ERROR>`) or anything
but an error (`<!UNDEFINED>`). Scalar cases are one call; aggregate cases a
call over a table; window cases a call over a frame whose rows are in the
order the function sees them.

For each case this module builds the call as a plan over a `VALUES`, has
`substrait-check` evaluate it (`--outcomes`, `Expr.evalP`, for scalars; the
rows of `Rel.eval` for aggregates and windows), and compares with the
expected result. A case that states no value for an option of its function
(by the YAML at the pinned commit) holds for every value: it is run once per
combination of the values it leaves open (the README: "the test should be run
for all permutations of the options").

`Profile.substrait.table` (`SubstraitLean/SubstraitProfile.lean`) chooses, at
every option of the YAMLs, the plan's first preference. Each run states every
option, so the reference's evaluator gives Substrait's outcome wherever the
parser accepts the preference (`Parse.optionAccepts`, which refuses the
others); it differs only at sverify's own options, where the two profiles
choose differently (`--profile-diff`: two zeros, NaN, `nan_creation`, …).
A case is

* `agree`: every run the checker accepts gives the expected result;
* `refused`: the checker (or this harness) refuses every run: a function, an
  option value or a type sverify does not model; the reason is counted;
* `disagree`: some run gives another result.

Each disagreement is triaged in the ledger
(`upstream/substrait-cases.json`): `profile` (the reference and Substrait
differ at the option it names; Substrait has no evaluator of its own, so it
counts as refused), `model` (a bug in sverify's model of Substrait: an issue),
`case` (a wrong test case: an `ST` tooling entry of `upstream/bugs/`) or
`gap` (behaviour Substrait leaves open: an `ST` spec gap). The ledger keeps
the totals per area, the refusals' reasons with counts, and the disagreements
one by one; `tests/test_substrait_cases.py` fails on a disagreement the
ledger does not list and on a ledger that is stale.

`fetch` checks out `tests/` and `extensions/` at `COMMIT` (sparse and
shallow, into `~/.cache/sverify/substrait-tests`). `python -m
sverify_dev.substrait_cases` prints the totals; `--write` rewrites the ledger,
keeping each disagreement's triage.
"""

from __future__ import annotations

import argparse
import base64
import datetime as dt
import functools
import itertools
import json
import math
import re
import subprocess
from collections import Counter
from collections.abc import Sequence
from dataclasses import dataclass, field
from decimal import Decimal
from pathlib import Path
from typing import Any

import yaml

from sverify.engine import run_checker

Json = dict[str, Any]

#: `substrait-io/substrait` at v0.106.0, the extensions `Profile.substrait`
#: reads (`SubstraitLean/SubstraitProfile.lean`).
TAG = "v0.106.0"
COMMIT = "b5aeda418813f657011bb82dd1300f996525c3ae"
REPO = "https://github.com/substrait-io/substrait.git"
CACHE = Path.home() / ".cache" / "sverify" / "substrait-tests"

ROOT = Path(__file__).resolve().parents[3]
LEDGER = ROOT / "upstream" / "substrait-cases.json"

#: The most combinations of open options run for one case.
MAX_RUNS = 64

#: The triage kinds of a disagreement, and how each counts in the totals.
KINDS = {"profile": "refused", "model": "disagree", "case": "disagree", "gap": "disagree"}


def fetch(dest: Path = CACHE) -> Path:
    """`tests/` and `extensions/` at `COMMIT`, checked out once."""
    if (dest / "tests" / "cases").is_dir() and _head(dest) == COMMIT:
        return dest
    if dest.exists():
        subprocess.run(["rm", "-rf", str(dest)], check=True)
    dest.parent.mkdir(parents=True, exist_ok=True)
    run = functools.partial(subprocess.run, check=True, capture_output=True)
    run(
        [
            "git",
            "clone",
            "-q",
            "--depth",
            "1",
            "--branch",
            TAG,
            "--filter=blob:none",
            "--sparse",
            REPO,
            str(dest),
        ]
    )
    run(["git", "-C", str(dest), "sparse-checkout", "set", "tests/cases", "extensions"])
    if _head(dest) != COMMIT:
        raise RuntimeError(f"{TAG} is {_head(dest)}, not {COMMIT}")
    return dest


def _head(dest: Path) -> str | None:
    r = subprocess.run(
        ["git", "-C", str(dest), "rev-parse", "HEAD"], capture_output=True, text=True
    )
    return r.stdout.strip() if r.returncode == 0 else None


# --------------------------------------------------------------------------
# The test format


@dataclass(frozen=True)
class Type:
    """A type as the cases write it: `i8`, `dec?<38,2>`, `list<i32?>`,
    `func<i32 -> bool>`, `u!u8`."""

    name: str
    nullable: bool = False
    params: tuple[Any, ...] = ()

    def __str__(self) -> str:
        ps = f"<{', '.join(map(str, self.params))}>" if self.params else ""
        return f"{self.name}{'?' if self.nullable else ''}{ps}"


@dataclass(frozen=True)
class Lit:
    """A literal: its text (a list's elements as a list) and its type."""

    value: Any
    type: Type


@dataclass(frozen=True)
class Column:
    """An aggregate case's column: `(1, 2, 3)::i8`."""

    values: tuple[Any, ...]
    type: Type


@dataclass(frozen=True)
class Ref:
    """`col0`, `t1.col1`, with the type a compact case gives it."""

    index: int
    type: Type | None = None


@dataclass(frozen=True)
class Enum:
    value: str


@dataclass(frozen=True)
class Lambda:
    param: str
    body: Any
    type: Type


@dataclass(frozen=True)
class Param:
    """A lambda's parameter in its body."""

    name: str


@dataclass(frozen=True)
class Call:
    name: str
    args: tuple[Any, ...]


ERROR = "<!ERROR>"
UNDEFINED = "<!UNDEFINED>"


@dataclass
class Case:
    file: str
    """The file, relative to `tests/cases`."""
    line: int
    text: str
    kind: str
    """`scalar`, `aggregate` or `window`."""
    call: Call
    options: dict[str, str]
    expected: Any
    """A `Lit`, a `Call`, a `Column` (a window's), `ERROR` or `UNDEFINED`."""
    table: tuple[tuple[Type, ...], tuple[tuple[Any, ...], ...]] | None = None
    """An aggregate's or a window's table: its columns' types and rows."""
    include: str = ""

    @property
    def area(self) -> str:
        return self.file.split("/")[0]

    @property
    def key(self) -> str:
        return f"{self.file}: {self.text}"


class FormatError(ValueError):
    pass


class _Quoted(str):
    """A string the case quoted: `'null'` is the text, not NULL."""


class _Reader:
    """A recursive-descent reader of one case's text."""

    def __init__(self, text: str, params: frozenset[str] = frozenset()):
        self.s = text
        self.i = 0
        self.params = params

    def ws(self) -> None:
        while self.i < len(self.s) and self.s[self.i].isspace():
            self.i += 1

    def peek(self, t: str) -> bool:
        self.ws()
        return self.s.startswith(t, self.i)

    def take(self, t: str) -> bool:
        if self.peek(t):
            self.i += len(t)
            return True
        return False

    def expect(self, t: str) -> None:
        if not self.take(t):
            raise FormatError(f"expected {t!r} at {self.s[self.i : self.i + 20]!r}")

    def ident(self) -> str:
        self.ws()
        m = re.compile(r"[A-Za-z_][A-Za-z0-9_.]*").match(self.s, self.i)
        if not m:
            raise FormatError(f"expected a name at {self.s[self.i : self.i + 20]!r}")
        self.i = m.end()
        return m.group()

    def type(self) -> Type:
        self.ws()
        m = re.compile(r"(u!)?[A-Za-z_][A-Za-z0-9_]*").match(self.s, self.i)
        if not m:
            raise FormatError(f"expected a type at {self.s[self.i : self.i + 20]!r}")
        self.i = m.end()
        nullable = self.take("?")
        params: list[Any] = []
        if self.take("<"):
            while not self.take(">"):
                self.ws()
                if m2 := re.compile(r"-?\d+").match(self.s, self.i):
                    self.i = m2.end()
                    params.append(int(m2.group()))
                else:
                    params.append(self.type())
                self.take(",") or self.take("->")
        return Type(m.group(), nullable, tuple(params))

    def raw(self, stop: str) -> Any:
        """An untyped value inside a list or a tuple: a string, a nested list,
        or text up to the next of `stop`."""
        self.ws()
        if self.peek("'"):
            return self.string()
        if self.take("["):
            return self.items("]")
        if self.take("("):
            return tuple(self.items(")"))
        j = self.i
        while self.i < len(self.s) and self.s[self.i] not in stop:
            self.i += 1
        return self.s[j : self.i].strip()

    def items(self, close: str) -> list[Any]:
        out: list[Any] = []
        while not self.take(close):
            out.append(self.raw(",)]"))
            self.take(",")
        return out

    def string(self) -> str:
        self.expect("'")
        out = []
        while self.s[self.i] != "'":
            if self.s[self.i] == "\\":
                self.i += 1
            out.append(self.s[self.i])
            self.i += 1
        self.i += 1
        return _Quoted("".join(out))

    def typed(self, value: Any) -> Any:
        self.expect("::")
        return Lit(value, self.type())

    def expr(self) -> Any:
        self.ws()
        if self.take(ERROR):
            return ERROR
        if self.take(UNDEFINED):
            return UNDEFINED
        if self.peek("'"):
            return self.typed(self.string())
        if self.take("["):
            return self.typed(self.items("]"))
        if m := re.compile(r"\(\s*(\w+)\s*->").match(self.s, self.i):
            self.i = m.end()
            body = _Reader(self.s, self.params | {m.group(1)})
            body.i = self.i
            b = body.expr()
            self.i = body.i
            self.expect(")")
            self.expect("::")
            return Lambda(m.group(1), b, self.type())
        if self.take("("):
            values = tuple(self.items(")"))
            self.expect("::")
            return Column(values, self.type())
        if m := re.compile(r"([A-Za-z_][A-Za-z0-9_]*)\s*\(").match(self.s, self.i):
            self.i = m.end()
            args = []
            while not self.take(")"):
                args.append(self.expr())
                self.take(",")
            return Call(m.group(1).lower(), tuple(args))
        if m := re.compile(r"(?:\w+\.)?col(\d+)\b").match(self.s, self.i):
            self.i = m.end()
            return Ref(int(m.group(1)), self.type() if self.take("::") else None)
        j = self.i
        while self.i < len(self.s) and not self.s.startswith("::", self.i):
            if self.s[self.i] in ",)" or self.s[self.i].isspace():
                break
            self.i += 1
        text = self.s[j : self.i]
        if text in self.params and not self.peek("::"):
            return Param(text)
        if self.peek("::"):
            self.expect("::")
            t = self.type()
            return Enum(text) if t.name == "enum" else Lit(text, t)
        raise FormatError(f"cannot read {self.s[j:]!r}")

    def options(self) -> dict[str, str]:
        opts: dict[str, str] = {}
        if self.take("["):
            while not self.take("]"):
                k = self.ident()
                self.expect(":")
                opts[k] = self.ident()
                self.take(",")
        return opts

    def comment(self) -> None:
        self.ws()
        if self.i < len(self.s) and not self.s.startswith("#", self.i):
            raise FormatError(f"trailing {self.s[self.i :]!r}")


def _table(r: _Reader, types: Sequence[Type] | None) -> tuple[tuple[Type, ...], tuple]:
    r.expect("(")
    rows = tuple(tuple(x) if isinstance(x, tuple) else (x,) for x in r.items(")"))
    # `(())` is a table of no rows.
    rows = tuple(row for row in rows if row)
    return (tuple(types) if types is not None else (), rows)


def parse_file(path: Path, root: Path) -> list[Case]:
    """The cases of one `.test` file."""
    rel = str(path.relative_to(root))
    kind = ""
    include = ""
    frames: dict[str, tuple] = {}
    cases: list[Case] = []
    for n, raw_line in enumerate(path.read_text().splitlines(), 1):
        line = raw_line.strip()
        if m := re.match(r"### SUBSTRAIT_(SCALAR|AGGREGATE|WINDOW)_TEST", line):
            kind = m.group(1).lower()
            continue
        if m := re.match(r"### SUBSTRAIT_INCLUDE:\s*(\S+)", line):
            include = m.group(1)
            continue
        if not line or line.startswith("#"):
            continue
        r = _Reader(line)
        if m := re.match(r"DEFINE\s+(\w+)\s*\(([^)]*)\)\s*=\s*", line):
            types = [_Reader(t).type() for t in m.group(2).split(",") if t.strip()]
            r.i = m.end()
            frames[m.group(1)] = _table(r, types)
            continue
        table = None
        if r.peek("("):
            table = _table(r, None)
        call = r.expr()
        if not isinstance(call, Call):
            raise FormatError(f"{rel}:{n}: not a call")
        if r.take("OVER"):
            table = frames[r.ident()]
        elif (
            table is None
            and frames
            and kind == "aggregate"
            and any(isinstance(a, Ref) for a in call.args)
        ):
            table = list(frames.values())[-1]
        opts = r.options()
        r.expect("=")
        expected = r.expr()
        r.comment()
        if table is not None and not table[0]:
            # A compact table: its columns are typed by the call's arguments.
            refs = {a.index: a.type for a in call.args if isinstance(a, Ref) and a.type}
            table = (tuple(refs[i] for i in sorted(refs)), table[1])
        cases.append(
            Case(rel, n, line.split(" #")[0].strip(), kind, call, opts, expected, table, include)
        )
    return cases


def parse_all(root: Path) -> tuple[list[Case], list[tuple[str, str]]]:
    """Every case under `root` (`tests/cases`), and the lines this reader
    cannot read."""
    cases: list[Case] = []
    errors: list[tuple[str, str]] = []
    for path in sorted(root.rglob("*.test")):
        try:
            cases += parse_file(path, root)
        except (FormatError, KeyError, IndexError) as e:
            errors.append((str(path.relative_to(root)), str(e)))
    return cases, errors


# --------------------------------------------------------------------------
# The YAMLs' options


@functools.cache
def _functions(ext_dir: Path) -> dict[str, list[Json]]:
    """Each function's impls, over every extension YAML."""
    found: dict[str, list[Json]] = {}
    for path in sorted(ext_dir.glob("*.yaml")):
        doc = yaml.safe_load(path.read_text())
        for kind in ("scalar_functions", "aggregate_functions", "window_functions"):
            for f in doc.get(kind) or []:
                found.setdefault(f["name"], []).extend(f.get("impls") or [])
    return found


#: The YAMLs' type names by the cases' short names.
_YAML_TYPES = {
    "bool": "boolean",
    "str": "string",
    "string": "string",
    "vchar": "varchar",
    "fchar": "fixedchar",
    "dec": "decimal",
    "pts": "precision_timestamp",
    "ptstz": "precision_timestamp_tz",
    "pt": "precision_time",
    "iyear": "interval_year",
    "iday": "interval_day",
    "date": "date",
    "list": "list",
    "func": "func",
}


def _arg_type(a: Any) -> Type | None:
    if isinstance(a, Lit | Column | Lambda):
        return a.type
    if isinstance(a, Ref):
        return a.type
    return None


def _matches(yaml_type: str, t: Type | None) -> bool:
    if t is None:
        return True
    y = yaml_type.split("<")[0].rstrip("?").lower()
    if y.startswith("any") or y == "t" or y.startswith("u!"):
        return True
    name = t.name.lower()
    return _YAML_TYPES.get(name, name) == y


def _fits(yaml_arg: Json, a: Any, t: Type | None) -> bool:
    if isinstance(a, Enum):
        return a.value in (yaml_arg.get("options") or [])
    return "value" in yaml_arg and _matches(yaml_arg["value"], t)


def impl_options(case: Case, ext_dir: Path) -> dict[str, list[str]] | None:
    """The options of the case's function at its arguments' types (the first
    impl that fits, enum arguments included); `None` if no impl fits."""
    impls = _functions(ext_dir).get(case.call.name, [])
    args = case.call.args
    types = [_arg_type(a) for a in args]
    if case.table is not None:
        types = [case.table[0][a.index] if isinstance(a, Ref) else _arg_type(a) for a in args]
    for impl in impls:
        params = impl.get("args") or []
        if len(params) == len(args) and all(
            _fits(p, a, t) for p, a, t in zip(params, args, types, strict=True)
        ):
            return {k: list(v["values"]) for k, v in (impl.get("options") or {}).items()}
    return None


def stray_options(case: Case, ext_dir: Path) -> list[str]:
    """The options the case states that its impl does not list."""
    opts = impl_options(case, ext_dir)
    if opts is None:
        return []
    return [f"{k}:{v}" for k, v in case.options.items() if v not in opts.get(k, [])]


def open_options(case: Case, ext_dir: Path) -> dict[str, list[str]]:
    """The options the case leaves open, with their values."""
    opts = impl_options(case, ext_dir) or {}
    return {k: v for k, v in opts.items() if k not in case.options}


def runs(case: Case, ext_dir: Path) -> list[dict[str, str]]:
    """The option settings to run the case under: what it states, and every
    combination of the values it leaves open."""
    open_ = open_options(case, ext_dir)
    names = sorted(open_)
    combos = list(itertools.islice(itertools.product(*(open_[n] for n in names)), MAX_RUNS))
    return [{**case.options, **dict(zip(names, c, strict=True))} for c in combos]


# --------------------------------------------------------------------------
# Plans

NULLABLE = {"nullability": "NULLABILITY_NULLABLE"}


class Refused(Exception):
    """This harness has no plan for the case."""


def type_json(t: Type) -> Json:
    n = t.name.lower()
    if n.startswith("u!"):
        raise Refused(f"unsigned integers ({t.name}) are not modelled")
    if n in ("i8", "i16", "i32", "i64", "fp32", "fp64", "date"):
        return {n: NULLABLE}
    if n in ("bool", "boolean"):
        return {"bool": NULLABLE}
    if n in ("str", "string"):
        return {"string": NULLABLE}
    if n == "vchar":
        return {"varchar": {"length": t.params[0], **NULLABLE}}
    if n == "fchar":
        return {"fixedChar": {"length": t.params[0], **NULLABLE}}
    if n == "dec":
        p, s = t.params or (38, 0)
        return {"decimal": {"precision": p, "scale": s, **NULLABLE}}
    if n in ("pts", "ptstz", "pt"):
        key = {"pts": "precisionTimestamp", "ptstz": "precisionTimestampTz", "pt": "precisionTime"}
        return {key[n]: {"precision": t.params[0] if t.params else 6, **NULLABLE}}
    if n == "iyear":
        return {"intervalYear": NULLABLE}
    if n == "iday":
        return {"intervalDay": {"precision": t.params[0] if t.params else 6, **NULLABLE}}
    if n == "list":
        return {"list": {"type": type_json(t.params[0]), **NULLABLE}}
    raise Refused(f"type {t} is not supported by this harness")


_FLOATS = {
    "inf": math.inf,
    "+inf": math.inf,
    "-inf": -math.inf,
    "nan": math.nan,
    "+nan": math.nan,
    "-nan": -math.nan,
    "snan": math.nan,
}
_TS = re.compile(r"(\d{4}-\d{2}-\d{2})[T ](\d{2}):(\d{2}):(\d{2})(\.\d+)?([+-]\d{2}:\d{2})?$")


def _subsecond(frac: str | None, precision: int) -> int:
    digits = (frac or ".")[1:]
    return int((digits + "0" * precision)[:precision] or 0)


def _iso_interval(text: str) -> tuple[int, int, Decimal]:
    """`P1Y2M3DT4H5M6.5S` as (months, days, seconds)."""
    m = re.fullmatch(
        r"P(?:(-?\d+)Y)?(?:(-?\d+)M)?(?:(-?\d+)D)?(?:T(?:(-?\d+)H)?(?:(-?\d+)M)?(?:(-?[\d.]+)S)?)?",
        text,
    )
    if not m:
        raise Refused(f"interval {text!r}")
    y, mo, d, h, mi, s = m.groups()
    secs = Decimal(h or 0) * 3600 + Decimal(mi or 0) * 60 + Decimal(s or 0)
    return int(y or 0) * 12 + int(mo or 0), int(d or 0), secs


def literal_body(v: Any, t: Type) -> Json:
    """A literal's body (without the `literal` key), of `v` read as `t`."""
    n = t.name.lower()
    if isinstance(v, str) and v.lower() == "null" and not isinstance(v, _Quoted):
        return {"null": type_json(t)}
    type_json(t)
    if n in ("i8", "i16", "i32"):
        return {n: int(v)}
    if n == "i64":
        return {n: str(int(v))}
    if n in ("fp32", "fp64"):
        x = _FLOATS.get(str(v).lower())
        x = float(v) if x is None else x
        text: Any = x
        if math.isnan(x):
            text = "NaN"
        elif math.isinf(x):
            text = "Infinity" if x > 0 else "-Infinity"
        return {n: text}
    if n in ("bool", "boolean"):
        if str(v).lower() not in ("true", "false"):
            raise Refused(f"boolean {v!r}")
        return {"boolean": str(v).lower() == "true"}
    if n in ("str", "string"):
        return {"string": str(v)}
    if n == "vchar":
        return {"varChar": {"value": str(v), "length": t.params[0]}}
    if n == "fchar":
        return {"fixedChar": str(v)}
    if n == "dec":
        p, s = t.params or (38, 0)
        unscaled = int(Decimal(str(v)).scaleb(s).to_integral_value())
        raw = base64.b64encode(unscaled.to_bytes(16, "little", signed=True)).decode()
        return {"decimal": {"value": raw, "precision": p, "scale": s}}
    if n == "date":
        return {"date": (dt.date.fromisoformat(str(v)) - dt.date(1970, 1, 1)).days}
    if n in ("pts", "ptstz"):
        m = _TS.match(str(v))
        if not m:
            raise Refused(f"timestamp {v!r}")
        p = t.params[0] if t.params else 6
        day, hh, mm, ss, frac, tz = m.groups()
        when = dt.datetime.fromisoformat(f"{day}T{hh}:{mm}:{ss}{tz or ''}")
        if when.tzinfo is not None:
            when = when.astimezone(dt.UTC).replace(tzinfo=None)
        secs = (when - dt.datetime(1970, 1, 1)) // dt.timedelta(seconds=1)
        value = secs * 10**p + _subsecond(frac, p)
        key = "precisionTimestamp" if n == "pts" else "precisionTimestampTz"
        return {key: {"precision": p, "value": str(value)}}
    if n == "pt":
        m = re.fullmatch(r"(\d{2}):(\d{2}):(\d{2})(\.\d+)?", str(v))
        if not m:
            raise Refused(f"time {v!r}")
        p = t.params[0] if t.params else 6
        secs = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + int(m.group(3))
        return {
            "precisionTime": {
                "precision": p,
                "value": str(secs * 10**p + _subsecond(m.group(4), p)),
            }
        }
    if n == "iyear":
        months, days, secs = _iso_interval(str(v))
        if days or secs:
            raise Refused(f"year-month interval {v!r}")
        return {"intervalYearToMonth": {"years": months // 12, "months": months % 12}}
    if n == "iday":
        months, days, secs = _iso_interval(str(v))
        if months:
            raise Refused(f"day-time interval {v!r}")
        p = t.params[0] if t.params else 6
        whole = int(secs)
        sub = int((secs - whole) * 10**p)
        return {
            "intervalDayToSecond": {
                "days": days,
                "seconds": whole,
                "subseconds": str(sub),
                "precision": p,
            }
        }
    if n == "list":
        if not isinstance(v, list):
            raise Refused(f"list {v!r}")
        if not v:
            return {"emptyList": {"type": type_json(t.params[0])}}
        return {"list": {"values": [literal_body(x, t.params[0]) for x in v]}}
    raise Refused(f"literal of type {t}")


class _Plan:
    """Function anchors of one plan."""

    def __init__(self) -> None:
        self.fns: dict[str, int] = {}

    def anchor(self, name: str) -> int:
        return self.fns.setdefault(name, len(self.fns) + 1)

    def expr(self, e: Any, opts: dict[str, str] | None = None, out: Type | None = None) -> Json:
        if isinstance(e, Lit):
            return {"literal": literal_body(e.value, e.type)}
        if isinstance(e, Ref):
            return _field(e.index)
        if isinstance(e, Param):
            return {
                "selection": {
                    "directReference": {"structField": {"field": 0}},
                    "lambdaParameterReference": {},
                }
            }
        if isinstance(e, Lambda):
            if len(e.type.params) != 2:
                raise Refused(f"lambda type {e.type}")
            params = {"types": [type_json(e.type.params[0])], "nullability": "NULLABILITY_REQUIRED"}
            return {"lambda": {"parameters": params, "body": self.expr(e.body)}}
        if isinstance(e, Call):
            return {"scalarFunction": self.function(e, opts or {}, out)}
        if isinstance(e, Column) and e.type.name.startswith("u!"):
            raise Refused(f"unsigned integers ({e.type.name}) are not modelled")
        if isinstance(e, Enum | Column):
            raise Refused(f"{type(e).__name__.lower()} argument outside its place")
        raise Refused(f"cannot plan {e!r}")

    def arg(self, a: Any) -> Json:
        if isinstance(a, Enum):
            return {"enum": a.value}
        return {"value": self.expr(a)}

    def function(self, c: Call, opts: dict[str, str], out: Type | None) -> Json:
        f: Json = {
            "functionReference": self.anchor(c.name),
            "arguments": [self.arg(a) for a in c.args],
        }
        if opts:
            f["options"] = [{"name": k, "preference": [v]} for k, v in opts.items()]
        if out is not None:
            f["outputType"] = type_json(out)
        return f

    def plan(self, root: Json, names: list[str]) -> str:
        exts = [
            {"extensionFunction": {"functionAnchor": a, "name": n}} for n, a in self.fns.items()
        ]
        return json.dumps(
            {"extensions": exts, "relations": [{"root": {"input": root, "names": names}}]}
        )


def _field(i: int) -> Json:
    return {"selection": {"directReference": {"structField": {"field": i}}, "rootReference": {}}}


def _values(types: Sequence[Type], rows: Sequence[Sequence[Any]]) -> Json:
    base = {
        "names": [f"c{i}" for i in range(len(types))],
        "struct": {"types": [type_json(t) for t in types], "nullability": "NULLABILITY_REQUIRED"},
    }
    table = {
        "expressions": [
            {"fields": [{"literal": literal_body(v, t)} for v, t in zip(r, types, strict=True)]}
            for r in rows
        ]
    }
    return {"read": {"baseSchema": base, "virtualTable": table}}


_ONE = (Type("i64"),), (("0",),)


def _project(input: Json, width: int, exprs: list[Json]) -> Json:
    emit = {"emit": {"outputMapping": list(range(width, width + len(exprs)))}}
    return {"project": {"input": input, "expressions": exprs, "common": emit}}


def _out_type(expected: Any) -> Type | None:
    return expected.type if isinstance(expected, Lit) else None


def scalar_plan(case: Case, opts: dict[str, str]) -> str:
    """A `Project` over a one-row `VALUES`: the call, then the expected
    result (a literal or a call), for `--outcomes`."""
    p = _Plan()
    exprs = [p.expr(case.call, opts, _out_type(case.expected))]
    if isinstance(case.expected, Lit | Call):
        exprs.append(p.expr(case.expected))
    return p.plan(_project(_values(*_ONE), 1, exprs), [f"r{i}" for i in range(len(exprs))])


def aggregate_plan(case: Case, opts: dict[str, str]) -> str:
    """The call as the measure of an `Aggregate` over its table, then the
    expected result as a literal beside it."""
    p = _Plan()
    args = list(case.call.args)
    if case.table is not None:
        types, rows = case.table
    else:
        cols = [a for a in args if isinstance(a, Column)]
        if len(cols) != 1:
            raise Refused("an aggregate case without one column")
        col = cols[0]
        types, rows = (col.type,), tuple((v,) for v in col.values)
        args = [Ref(0) if isinstance(a, Column) else a for a in args]
    measure: Json = {
        "functionReference": p.anchor(case.call.name),
        "arguments": [p.arg(a) for a in args],
        "invocation": "AGGREGATION_INVOCATION_ALL",
        "phase": "AGGREGATION_PHASE_INITIAL_TO_RESULT",
    }
    if opts:
        measure["options"] = [{"name": k, "preference": [v]} for k, v in opts.items()]
    if (t := _out_type(case.expected)) is not None:
        measure["outputType"] = type_json(t)
    agg = {
        "aggregate": {
            "input": _values(types, rows),
            "groupings": [],
            "measures": [{"measure": measure}],
        }
    }
    exprs = [_field(0)]
    if isinstance(case.expected, Lit):
        exprs.append(p.expr(case.expected))
        if (near := _near(case.expected)) is not None:
            exprs.append(p.expr(near))
    return p.plan(_project(agg, 1, exprs), [f"r{i}" for i in range(len(exprs))])


#: How far a double may lie from the expected value, relative to it: the
#: digits an `fp32` literal is written with, and a few units in the last place
#: of an `fp64` (Substrait names no algorithm for `sum`, `avg`, `variance`, …).
TOLERANCE = {"fp32": 2.0**-23, "fp64": 4 * 2.0**-52}


def _near(want: Lit) -> Call | None:
    """`|col0 - want| <= tol`, which Lean decides exactly (it prints doubles
    with six digits), for a finite double `want`."""
    if want.type.name not in TOLERANCE or str(want.value).lower() == "null":
        return None
    x = _FLOATS.get(str(want.value).lower())
    x = float(want.value) if x is None else x
    if not math.isfinite(x):
        return None
    fp64 = Type("fp64")
    diff = Call("abs", (Call("subtract", (Ref(0), Lit(repr(x), fp64))),))
    return Call("lte", (diff, Lit(repr(abs(x) * TOLERANCE[want.type.name]), fp64)))


def window_plan(case: Case, opts: dict[str, str]) -> str:
    """The call over its frame: a `VALUES` with the rows' positions first,
    the expected column last, a window ordered by position over the whole
    partition."""
    assert case.table is not None
    types, rows = case.table
    exp = case.expected
    if not isinstance(exp, Column):
        raise Refused("a window case's result is not a column")
    if len(exp.values) != len(rows):
        raise Refused("a window case's result has another number of rows")
    p = _Plan()
    cols = (Type("i64"), *types, exp.type)
    data = [(str(i), *r, e) for i, (r, e) in enumerate(zip(rows, exp.values, strict=True))]
    args = [Ref(a.index + 1) if isinstance(a, Ref) else a for a in case.call.args]
    w: Json = {
        "functionReference": p.anchor(case.call.name),
        "arguments": [p.arg(a) for a in args],
        "partitions": [],
        "sorts": [{"expr": _field(0), "direction": "SORT_DIRECTION_ASC_NULLS_LAST"}],
        "lowerBound": {"unbounded": {}},
        "upperBound": {"unbounded": {}},
        "boundsType": "BOUNDS_TYPE_ROWS",
        "outputType": type_json(exp.type),
    }
    if opts:
        w["options"] = [{"name": k, "preference": [v]} for k, v in opts.items()]
    width = len(cols)
    win = {"project": {"input": _values(cols, data), "expressions": [{"windowFunction": w}]}}
    root = _project(win, width + 1, [_field(0), _field(width), _field(width - 1)])
    return p.plan(root, ["pos", "got", "want"])


# --------------------------------------------------------------------------
# Running


@dataclass
class Outcome:
    cls: str
    """`agree`, `refused` or `disagree`."""
    reason: str = ""
    got: str = ""
    options: dict[str, str] = field(default_factory=dict)


def _why(out: str, err: str) -> str:
    lines = (err or out).strip().splitlines() or ["?"]
    text = re.sub(r"^error: ", "", lines[-1])
    # Literal values vary per case; the reason is the same.
    return re.sub(r"\d+(\.\d+)?", "N", text)[:160]


def _scalar(case: Case, opts: dict[str, str]) -> Outcome:
    code, out, err = run_checker(("--outcomes",), scalar_plan(case, opts))
    if code != 0:
        return Outcome("refused", "checker: " + _why(out, err), options=opts)
    ((*row,),) = [json.loads(line) for line in out.splitlines()]
    got = row[0]
    want = case.expected
    shown = _show(got, want)
    if "ok" in got and want in (UNDEFINED, ERROR) and (why := _panics(case, opts)):
        return Outcome("refused", why, options=opts)
    if want == UNDEFINED:
        return Outcome("agree" if "ok" in got else "disagree", got=shown, options=opts)
    if want == ERROR:
        return Outcome("agree" if "error" in got else "disagree", got=shown, options=opts)
    exp = row[1]
    if "error" in exp:
        return Outcome(
            "refused", f"checker: the expected result raises ({exp['error']})", options=opts
        )
    if "ok" in got and (why := _panics(case, opts)):
        return Outcome("refused", why, options=opts)
    if got == exp:
        return Outcome("agree", got=shown, options=opts)
    if "ok" in got and isinstance(want, Lit) and want.type.name == "dec":
        # Two scales of one value: compare as rendered by kind.
        code, out, _ = run_checker((), scalar_plan(case, opts))
        if code == 0:
            from sverify.testing import parse_rows

            ((a, b),) = parse_rows(out)
            if a is not None and b is not None and Decimal(str(a)) == Decimal(str(b)):
                return Outcome("agree", got=str(a), options=opts)
            shown = str(a)
    return Outcome("disagree", got=shown, options=opts)


def _show(outcome: Json, want: Any) -> str:
    """An outcome as the ledger shows it: a double as a number, not its code."""
    v = outcome.get("ok")
    if isinstance(want, Lit) and want.type.name in TOLERANCE and isinstance(v, int):
        from sverify.contracts import decode_double

        return repr(decode_double(v))
    return json.dumps(outcome["ok"] if "ok" in outcome else {"error": outcome["error"]})


def _panics(case: Case, opts: dict[str, str]) -> str:
    """Why `Rel.eval` gives no value, if it does not: `--outcomes` goes on
    past the black boxes Lean does not evaluate (`Main.check`)."""
    code, out, err = run_checker((), scalar_plan(case, opts))
    if code != 0 and "not evaluated" in err:
        return "checker: " + _why(out, err)
    return ""


def _rows(case: Case, plan: str, opts: dict[str, str]) -> tuple[Outcome | None, list[tuple]]:
    code, out, err = run_checker((), plan)
    if code != 0 or "well-formed: yes" not in out:
        return Outcome("refused", "checker: " + _why(out, err), options=opts), []
    from sverify.testing import parse_rows

    try:
        return None, parse_rows(out, doubles=True)
    except (ValueError, IndexError) as e:
        return Outcome("refused", f"harness: cannot read the rows ({e})", options=opts), []


def _aggregate(case: Case, opts: dict[str, str]) -> Outcome:
    early, rows = _rows(case, aggregate_plan(case, opts), opts)
    if early is not None:
        return early
    ((got, *rest),) = rows
    if case.expected == ERROR:
        # `Rel.eval` gives NULL where the reference raises; `verify` says why.
        return _aggregate_error(case, opts, got)
    if case.expected == UNDEFINED:
        return Outcome("agree", got=repr(got), options=opts)
    if len(rest) == 2:
        # A double: within `TOLERANCE` of the expected value.
        return Outcome("agree" if rest[1] is True else "disagree", got=repr(got), options=opts)
    (want,) = rest
    return Outcome("agree" if _same(got, want) else "disagree", got=repr(got), options=opts)


def _aggregate_error(case: Case, opts: dict[str, str], got: Any) -> Outcome:
    plan = json.loads(aggregate_plan(case, opts))
    code, out, err = run_checker(("--contract",), json.dumps({"transform": plan, "ensures": []}))
    try:
        report = json.loads(out)
    except json.JSONDecodeError:
        return Outcome("refused", "checker: " + _why(out, err), options=opts)
    issues = [i for i in report.get("issues", []) if i.get("error", True)]
    return Outcome("agree" if issues else "disagree", got=repr(got), options=opts)


def _window(case: Case, opts: dict[str, str]) -> Outcome:
    early, rows = _rows(case, window_plan(case, opts), opts)
    if early is not None:
        return early
    rows.sort(key=lambda r: r[0])
    ok = all(_same(g, w) for _, g, w in rows)
    return Outcome("agree" if ok else "disagree", got=repr([g for _, g, _ in rows]), options=opts)


def _same(a: Any, b: Any) -> bool:
    if isinstance(a, float) and isinstance(b, float):
        return a == b or (math.isnan(a) and math.isnan(b))
    if isinstance(a, int | float | Decimal) and isinstance(b, int | float | Decimal):
        return Decimal(str(a)) == Decimal(str(b))
    return a == b


def run_once(case: Case, opts: dict[str, str]) -> Outcome:
    try:
        if case.kind == "scalar":
            return _scalar(case, opts)
        if case.kind == "aggregate":
            return _aggregate(case, opts)
        return _window(case, opts)
    except Refused as e:
        return Outcome("refused", f"harness: {e}", options=opts)


@dataclass
class Result:
    case: Case
    cls: str
    reason: str = ""
    runs: int = 0
    failing: list[Outcome] = field(default_factory=list)


def run_case(case: Case, ext_dir: Path) -> Result:
    """Every run of the case, folded: a disagreement in any run is the
    case's; it agrees when some run was accepted and none disagrees."""
    if stray := stray_options(case, ext_dir):
        # A value the YAML does not offer: the case, not the model, is wrong.
        why = Outcome("disagree", got=f"not in the YAML: {', '.join(stray)}", options=case.options)
        return Result(case, "disagree", runs=0, failing=[why])
    outs = [run_once(case, o) for o in runs(case, ext_dir) or [dict(case.options)]]
    bad = [o for o in outs if o.cls == "disagree"]
    if bad:
        return Result(case, "disagree", runs=len(outs), failing=bad)
    if any(o.cls == "agree" for o in outs):
        return Result(case, "agree", runs=len(outs))
    reasons = Counter(o.reason for o in outs)
    return Result(case, "refused", reason=reasons.most_common(1)[0][0], runs=len(outs))


def run_all(root: Path | None = None) -> tuple[list[Result], list[tuple[str, str]]]:
    root = root or fetch()
    cases, errors = parse_all(root / "tests" / "cases")
    ext = root / "extensions"
    return [run_case(c, ext) for c in cases], errors


# --------------------------------------------------------------------------
# The ledger


def _failure(r: Result) -> Json:
    o = r.failing[0]
    return {
        "case": r.case.key,
        "options": o.options,
        "got": o.got,
        "runs": f"{len(r.failing)} of {r.runs}",
    }


def ledger(
    results: Sequence[Result], errors: Sequence[tuple[str, str]], old: Json | None = None
) -> Json:
    """The ledger of `results`: totals per area, refusals by reason, and the
    disagreements with their triage from `old`."""
    triage = {
        d["case"]: {k: d[k] for k in ("kind", "ref", "note") if k in d}
        for d in (old or {}).get("disagreements", [])
    }
    totals: dict[str, Counter[str]] = {}
    refusals: dict[str, Counter[str]] = {}
    disagreements = []
    for r in results:
        cls = r.cls
        if cls == "disagree":
            d = {**_failure(r), **triage.get(r.case.key, {"kind": "untriaged"})}
            disagreements.append(d)
            cls = KINDS.get(d["kind"], "disagree")
        totals.setdefault(r.case.area, Counter())[cls] += 1
        if r.cls == "refused":
            refusals.setdefault(r.case.area, Counter())[r.reason] += 1
    total = sum(totals.values(), Counter())
    return {
        "substrait": {"tag": TAG, "commit": COMMIT},
        "totals": {
            a: {k: c[k] for k in ("agree", "refused", "disagree")}
            for a, c in [*sorted(totals.items()), ("all", total)]
        },
        "unread": [{"file": f, "error": e} for f, e in errors],
        "refusals": {
            a: dict(sorted(c.items(), key=lambda kv: (-kv[1], kv[0])))
            for a, c in sorted(refusals.items())
        },
        "disagreements": sorted(disagreements, key=lambda d: d["case"]),
    }


def read_ledger(path: Path = LEDGER) -> Json:
    return json.loads(path.read_text()) if path.exists() else {}


def write_ledger(data: Json, path: Path = LEDGER) -> None:
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")


def table(data: Json) -> str:
    """The totals as a Markdown table."""
    lines = ["| Area | Agree | Refused | Disagree |", "|---|---:|---:|---:|"]
    for area, t in data["totals"].items():
        lines.append(f"| {area} | {t['agree']} | {t['refused']} | {t['disagree']} |")
    return "\n".join(lines)


def main(argv: Sequence[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--write", action="store_true", help="rewrite the ledger")
    ap.add_argument("--root", type=Path, help="a checkout of substrait-io/substrait at COMMIT")
    ap.add_argument("--show", metavar="AREA", help="print each case of an area with its class")
    args = ap.parse_args(argv)
    results, errors = run_all(args.root)
    data = ledger(results, errors, read_ledger())
    if args.show:
        for r in results:
            if r.case.area == args.show:
                extra = r.reason or (r.failing[0].got if r.failing else "")
                print(f"{r.cls:8} {r.case.text}  {extra}")
    print(table(data))
    for d in data["disagreements"]:
        print(f"{d['kind']:10} {d['case']}  {d['options']}  got {d['got']}")
    for u in data["unread"]:
        print(f"unread {u['file']}: {u['error']}")
    if args.write:
        write_ledger(data)


if __name__ == "__main__":
    main()

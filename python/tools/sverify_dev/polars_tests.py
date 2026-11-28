"""Replay Polars's own unit tests through sverify, as outside evidence (#2615).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

Polars's Python tests (`py-polars/tests/unit`, MIT) run Polars queries on
inputs Polars's developers chose and assert their results. This module runs a
slice of them (`MODULES`, the operations sverify covers) at the Polars
release `python/uv.lock` pins (`TAG`), and loads itself as a pytest plugin
(`-p sverify_dev.polars_tests`). Each `LazyFrame.collect` a passing test makes (and
each eager operation, which goes through `LazyFrame._collect_eager`) is
captured as Polars's plan (`LazyFrame.serialize(format="json")`, the DSL), its
inputs and its result. The translator (`translate`) writes the plan as an
Ibis expression over the inputs, for the plan nodes and expressions it knows,
and sverify verifies it under `semantics="polars"`. Three results are then
compared, as bags of rows (a sort's keys in order, ties open):

* `polars`: the collect's own result, Polars's result on its developers'
  inputs. A passing test vouches only for what it asserts, so this is not an
  expected value;
* `lean`: `Rel.evalChoices` (`substrait-check --eval-choices`) of the
  verified plan with the inputs inlined, the model under `Profile.polars`;
* `engine`: sverify's run of the verified plan on Polars (`Report.run`).

Each collect is (ruling 288, P1-P5):

* `agree`: `lean`, `engine` and `polars` give the same rows;
* `disagree`: `lean` and `engine` differ (`side` says which matches
  `polars`). Both ran the same translated plan, so the translator is not
  involved: a model or lowering finding;
* `unattributed`: `lean` and `engine` agree and differ from `polars`. The
  translator, or a gap between `semantics="polars"` and the in-memory engine
  the tests use, is the cause. Each is triaged by hand in `triage.json`: into
  `skipped: translation` (the node and the reason named), a fact or a bug.
  The gate fails on one that is not triaged;
* `refused` and `unproved`: sverify refuses the expression, or does not
  prove it (after the preconditions it suggests, as a user would);
* `skipped`: the translator does not read a node (`translator: …`), the
  inputs or the result hold a value the model lacks, the collect raises
  (`raises`), or the test is a Hypothesis test (its inputs change each run).

A test's outcome is its worst collect's. `python -m sverify_dev.polars_tests`
fetches the tests (into `~/.cache/sverify/polars-tests`), replays the modules,
prints the totals and with `--write` rewrites the ledgers
`engines/polars/replay/<module>.json`. `--check` fails on a new disagreement,
on an untriaged `unattributed` collect and on a test that agreed and no
longer does. It runs the checker on every captured plan: run it on homelab
(`homelab-run`), with a module or two at a time on the laptop.
"""

from __future__ import annotations

import argparse
import collections
import contextlib
import datetime as dt
import hashlib
import io
import json
import math
import os
import subprocess
import sys
import tempfile
import warnings
from collections.abc import Callable, Iterable, Sequence
from pathlib import Path
from typing import Any

from sverify_dev.ibis_replay import normalize

ROOT = Path(__file__).resolve().parents[3]
LEDGERS = ROOT / "engines" / "polars" / "replay"
TRIAGE = LEDGERS / "triage.json"
REPO = "https://github.com/pola-rs/polars"
#: The Polars release `python/uv.lock` pins, and its commit.
TAG = "py-2.1.0"
COMMIT = "7f902bd3ffd27ff82d14278a09a295ff2f7aed92"
TESTS = "py-polars/tests"
CACHE = Path(
    os.environ.get("SVERIFY_POLARS_TESTS", Path.home() / ".cache" / "sverify" / "polars-tests")
)

#: The test modules replayed, under `tests/unit/`: the operations sverify
#: covers (#2615's slice).
MODULES = (
    "operations/arithmetic",
    "operations/aggregation",
    "operations/test_filter.py",
    "operations/test_sort.py",
    "operations/test_join.py",
    "operations/test_group_by.py",
    "operations/test_over.py",
    "operations/test_window.py",
    "operations/test_is_null.py",
    "operations/test_fill_null.py",
    "operations/test_cast.py",
    "operations/test_is_in.py",
    "operations/test_comparison.py",
    "operations/unique",
    "operations/test_with_columns.py",
    "operations/test_select.py",
    "expr",
    "functions",
)

OUTCOMES = ("agree", "disagree", "unattributed", "refused", "unproved", "skipped")
#: How bad an outcome is, worst first, for a test's worst collect.
_RANK = {"disagree": 0, "unattributed": 1, "refused": 2, "unproved": 3, "agree": 4, "skipped": 5}
#: The collects of one test replayed at most; the rest are counted only.
MAX_COLLECTS = 8
#: The input rows a collect inlines into the checker at most: a larger one is
#: skipped (the checker evaluates virtual tables, which a large input slows).
MAX_ROWS = 200
#: The size of a captured plan in Polars's binary form at most.
MAX_PLAN_BYTES = 256 * 1024


# -- the sources ---------------------------------------------------------------


def fetch(tag: str = TAG, cache: Path = CACHE) -> Path:
    """Polars's `py-polars` directory at `tag`, with its tests, cloned into
    `cache` on first use (a sparse, blobless clone of the tests only)."""
    root = cache / tag
    if not (root / TESTS).is_dir():
        cache.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["git", "clone", "-q", "--depth", "1", "--branch", tag, "--filter=blob:none",
             "--sparse", REPO, str(root)],
            check=True,
        )  # fmt: skip
        subprocess.run(["git", "-C", str(root), "sparse-checkout", "set", TESTS], check=True)
    head = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "HEAD"], capture_output=True, text=True, check=True
    ).stdout.strip()
    if tag == TAG and head != COMMIT:
        raise SystemExit(f"{root} is at {head}, not {TAG}'s {COMMIT}: delete it and fetch again")
    return root / "py-polars"


def replay(
    modules: Sequence[str], workers: int = 2, out: Path | None = None
) -> list[dict[str, Any]]:
    """Run Polars's tests of `modules` with this module as a plugin, one
    pytest process per module (so memory starts afresh), and append one record
    per test to `out` (a temporary file if None) as each test ends: a run that
    stops keeps what it replayed."""
    here = fetch()
    with tempfile.TemporaryDirectory() as tmp:
        out = out or Path(tmp) / "replay.jsonl"
        env = {
            **os.environ,
            "SVERIFY_POLARS_TESTS_OUT": str(out),
            "PYTHONPATH": os.pathsep.join([str(ROOT / "python" / "tools"), str(here)]),
        }
        for module in modules:
            cmd = [
                sys.executable, "-m", "pytest", "-q",
                "-p", "no:sverify", "-p", "no:cacheprovider", "-p", "sverify_dev.polars_tests",
                "-o", "addopts=", "-o", "filterwarnings=ignore", "-o", "xfail_strict=false",
                *(["-n", str(workers)] if workers > 1 else []),
                f"tests/unit/{module}",
            ]  # fmt: skip
            subprocess.run(cmd, cwd=here, env=env, check=False, stdout=subprocess.DEVNULL)
            print(f"replayed {module}", file=sys.stderr, flush=True)
        if not out.exists():
            raise SystemExit("the replay wrote nothing: run pytest by hand to see why")
        return [json.loads(line) for line in out.read_text().splitlines() if line.strip()]


# -- the translator --------------------------------------------------------------


class Untranslated(Exception):
    """A node of Polars's plan the translator does not read."""


def _key(node: Any) -> str:
    """The variant of a DSL node: its single key, or the string itself."""
    if isinstance(node, str):
        return node
    if isinstance(node, dict) and len(node) == 1:
        return next(iter(node))
    raise Untranslated(f"node {str(node)[:60]}")


def _frame(raw: Sequence[int]) -> Any:
    """A `DataFrameScan`'s frame: its Arrow IPC stream."""
    import polars as pl

    return pl.read_ipc_stream(io.BytesIO(bytes(raw)))


#: Polars's binary operators, as Ibis's.
_BINARY: dict[str, Callable[[Any, Any], Any]] = {
    "Plus": lambda a, b: a + b,
    "Minus": lambda a, b: a - b,
    "Multiply": lambda a, b: a * b,
    "TrueDivide": lambda a, b: a / b,
    "FloorDivide": lambda a, b: a // b,
    "Modulus": lambda a, b: a % b,
    "Eq": lambda a, b: a == b,
    "NotEq": lambda a, b: a != b,
    "Lt": lambda a, b: a < b,
    "LtEq": lambda a, b: a <= b,
    "Gt": lambda a, b: a > b,
    "GtEq": lambda a, b: a >= b,
    "And": lambda a, b: a & b,
    "Or": lambda a, b: a | b,
    "LogicalAnd": lambda a, b: a & b,
    "LogicalOr": lambda a, b: a | b,
    "EqValidity": lambda a, b: a.identical_to(b),
    "NotEqValidity": lambda a, b: ~a.identical_to(b),
}

#: Polars's aggregates of one input, as Ibis's reductions.
_AGGS: dict[str, Callable[[Any], Any]] = {
    "Sum": lambda x: x.sum(),
    "Mean": lambda x: x.mean(),
    "Min": lambda x: x.min(),
    "Max": lambda x: x.max(),
    # Polars counts NULL as one more value, Ibis does not.
    "NUnique": lambda x: x.nunique() + x.isnull().any().cast("int64"),
}

#: Polars's functions of one input, as Ibis's.
_UNARY: dict[str, Callable[[Any], Any]] = {
    "IsNull": lambda x: x.isnull(),
    "IsNotNull": lambda x: x.notnull(),
    "Not": lambda x: ~x,
    "IsNan": lambda x: x.isnan(),
    "IsFinite": lambda x: ~(x.isnan() | x.isinf()),
    "IsInfinite": lambda x: x.isinf(),
    "Abs": lambda x: x.abs(),
    "Negate": lambda x: -x,
    "Uppercase": lambda x: x.upper(),
    "Lowercase": lambda x: x.lower(),
    "LenChars": lambda x: x.length(),
}

#: Polars's dtypes in a cast, as Ibis's.
_DTYPES = {
    "Int8": "int8",
    "Int16": "int16",
    "Int32": "int32",
    "Int64": "int64",
    "UInt8": "uint8",
    "UInt16": "uint16",
    "UInt32": "uint32",
    "UInt64": "uint64",
    "Float32": "float32",
    "Float64": "float64",
    "Boolean": "boolean",
    "String": "string",
    "Date": "date",
}


def _is_null(e: Any) -> bool:
    """`e` is a NULL literal, of no type or of a dtype (`{"Null": "Int64"}`)."""
    lit = e.get("Literal") if isinstance(e, dict) else None
    return isinstance(lit, dict) and isinstance(lit.get("Scalar"), dict) and "Null" in lit["Scalar"]


def _aggregates(e: Any) -> bool:
    """`e` reduces its input to one value: an aggregate or `len` not under
    `over`, or an expression of such."""
    k = _key(e)
    if k in ("Agg", "Len"):
        return True
    if k in ("Over", "Column", "Literal", "Selector"):
        return False
    v: Any = e[k] if isinstance(e, dict) else None
    if k == "Alias":
        return _aggregates(v[0])
    if k == "BinaryExpr":
        return _aggregates(v["left"]) or _aggregates(v["right"])
    if k == "Cast":
        return _aggregates(v["expr"])
    if k == "Function":
        return any(_aggregates(a) for a in v["input"])
    if k == "Ternary":
        return any(_aggregates(v[x]) for x in ("predicate", "truthy", "falsy"))
    return False


def _reads_columns(e: Any) -> bool:
    """`e` reads a column of its input (a selector reads them all)."""
    if isinstance(e, dict):
        return "Column" in e or "Selector" in e or any(_reads_columns(v) for v in e.values())
    if isinstance(e, list):
        return any(_reads_columns(v) for v in e)
    return e == "Len"


def output_name(e: Any) -> str:
    """The name Polars gives the column of the expression `e` (its leftmost
    input's, an alias's, `literal` or `len`)."""
    k = _key(e)
    v: Any = e[k] if isinstance(e, dict) else None
    if k == "Alias":
        return v[1]
    if k == "Column":
        return v
    if k == "Literal":
        return "literal"
    if k == "Len":
        return "len"
    if k == "BinaryExpr":
        return output_name(v["left"])
    if k == "Ternary":
        return output_name(v["truthy"])
    if k == "Cast":
        return output_name(v["expr"])
    if k == "Function":
        return output_name(v["input"][0])
    if k == "Agg":
        inner = v[_key(v)]
        if isinstance(inner, dict) and "input" in inner:
            inner = inner["input"]
        elif isinstance(inner, list):
            inner = inner[0]
        return output_name(inner)
    if k == "Over":
        return output_name(v["function"])
    raise Untranslated(f"the name of {k}")


class Translator:
    """Polars's DSL plan as an Ibis expression over the tables of `con`: each
    `DataFrameScan`'s frame is put into it as a table of its own."""

    def __init__(self, con: Any) -> None:
        self.con = con
        self.inputs: dict[str, Any] = {}

    def relation(self, node: Any) -> Any:
        k = _key(node)
        v = node[k]
        method = getattr(self, f"rel_{k}", None)
        if method is None:
            raise Untranslated(k)
        return method(v)

    # Relations

    def rel_DataFrameScan(self, v: Any) -> Any:
        import pyarrow as pa

        frame = _frame(v["df"])
        name = f"polars_input_{len(self.inputs)}"
        if not frame.columns:
            raise Untranslated("inputs: a frame with no columns")
        try:
            arrow = frame.to_arrow()
        except Exception as e:  # noqa: BLE001 - a type Arrow does not hold
            raise Untranslated(f"inputs: {type(e).__name__}") from e
        if sum(t.num_rows for t in self.inputs.values()) + arrow.num_rows > MAX_ROWS:
            raise Untranslated(f"inputs: more than {MAX_ROWS} rows")
        if any(pa.types.is_dictionary(f.type) for f in arrow.schema):
            # A categorical sorts and compares by its own rules (#2615).
            raise Untranslated("inputs: a categorical column")
        self.inputs[name] = arrow
        self.con.put(name, arrow)
        return self.con.table(name)

    def rel_Select(self, v: Any) -> Any:
        rel = self.relation(v["input"])
        kinds = {_aggregates(e) for e in v["expr"]}
        if kinds == {True}:
            # A select of aggregates only is one row, as an aggregate of no keys.
            return rel.aggregate(self.named(rel, v["expr"], aggregate=True))
        if True in kinds:
            raise Untranslated("a select of aggregates and columns (a broadcast)")
        if not any(_reads_columns(e) for e in v["expr"]):
            raise Untranslated("a select of literals only: one row in Polars")
        return rel.select(*self.named(rel, v["expr"]))

    def rel_HStack(self, v: Any) -> Any:
        rel = self.relation(v["input"])
        return rel.mutate(*self.named(rel, v["exprs"]))

    def rel_Filter(self, v: Any) -> Any:
        rel = self.relation(v["input"])
        return rel.filter(self.expr(rel, v["predicate"]))

    def rel_Sort(self, v: Any) -> Any:
        if v.get("slice") is not None:
            raise Untranslated("Sort with a slice")
        rel = self.relation(v["input"])
        opts = v["sort_options"]
        keys = []
        for i, e in enumerate(v["by_column"]):
            x = self.expr(rel, e)
            nulls_first = not opts["nulls_last"][i]
            keys.append(
                x.desc(nulls_first=nulls_first)
                if opts["descending"][i]
                else x.asc(nulls_first=nulls_first)
            )
        return rel.order_by(keys)

    def rel_Slice(self, v: Any) -> Any:
        if _key(v["input"]) != "Sort" or v["offset"] < 0:
            raise Untranslated("Slice without a Sort below it")
        return self.relation(v["input"]).limit(v["len"], offset=v["offset"])

    def rel_GroupBy(self, v: Any) -> Any:
        opts = v.get("options") or {}
        if v.get("apply") or opts.get("dynamic") or opts.get("rolling") or opts.get("slice"):
            raise Untranslated("GroupBy with apply, a dynamic or rolling window or a slice")
        if v.get("predicates"):
            raise Untranslated("GroupBy with predicates")
        rel = self.relation(v["input"])
        keys = self.named(rel, v["keys"])
        aggs = self.named(rel, v["aggs"], aggregate=True)
        return rel.group_by(keys).aggregate(aggs)

    def rel_Distinct(self, v: Any) -> Any:
        opts = v["options"]
        if opts.get("subset") is not None or opts["keep_strategy"] not in ("Any", "None"):
            raise Untranslated("Distinct with a subset or a keep strategy")
        return self.relation(v["input"]).distinct()

    def rel_Union(self, v: Any) -> Any:
        import ibis

        args = v["args"]
        if args.get("diagonal") or args.get("to_supertypes"):
            raise Untranslated("Union, diagonal or to supertypes")
        rels = [self.relation(r) for r in v["inputs"]]
        return ibis.union(*rels, distinct=False)

    def rel_Join(self, v: Any) -> Any:
        args = v["options"]["args"]
        how = {"Inner": "inner", "Left": "left", "Semi": "semi", "Anti": "anti"}.get(args["how"])
        if how is None or args.get("slice") is not None or args.get("nulls_equal"):
            raise Untranslated(f"Join {args['how']}")
        cond = v.get("condition") or {}
        if _key(cond) != "Equi":
            raise Untranslated("Join without an equi condition")
        left, right = self.relation(v["input_left"]), self.relation(v["input_right"])
        lk = [self.expr(left, e) for e in cond["Equi"]["left_on"]]
        rk = [self.expr(right, e) for e in cond["Equi"]["right_on"]]
        same_names = [
            output_name(a) == output_name(b)
            for a, b in zip(cond["Equi"]["left_on"], cond["Equi"]["right_on"], strict=True)
        ]
        joined = left.join(
            right,
            [a == b for a, b in zip(lk, rk, strict=True)],
            how=how,
            rname="{name}" + args.get("suffix", "_right"),
        )
        if how in ("semi", "anti"):
            return joined
        # Polars keeps the left key and drops the right one of the same name
        # (`coalesce` for inner and left joins); every other right column that
        # clashes takes the suffix.
        if not all(same_names) or args.get("coalesce") == "KeepColumns":
            raise Untranslated("Join on keys of different names, or keeping both keys")
        keys = {output_name(e) for e in cond["Equi"]["right_on"]}
        suffix = args.get("suffix", "_right")
        names = list(left.columns) + [
            (c + suffix if c in left.columns else c) for c in right.columns if c not in keys
        ]
        return joined.select(*[joined[n] for n in names])

    def rel_MapFunction(self, v: Any) -> Any:
        f = v["function"]
        k = _key(f)
        rel = self.relation(v["input"])
        if k == "Rename":
            return rel.rename(dict(zip(f[k]["new"], f[k]["existing"], strict=True)))
        raise Untranslated(f"MapFunction {k}")

    # Expressions

    def named(self, rel: Any, exprs: Iterable[Any], aggregate: bool = False) -> list[Any]:
        out = []
        for e in exprs:
            if _key(e) == "Selector":
                out += [rel[c] for c in self.selected(rel, e["Selector"])]
                continue
            x = self.expr(rel, e, aggregate=aggregate)
            out.append(x.name(output_name(e)))
        return out

    def selected(self, rel: Any, sel: Any) -> list[str]:
        if sel == "Wildcard":
            return list(rel.columns)
        k = _key(sel)
        v = sel[k]
        if k == "ByName":
            return list(v["names"])
        if k == "Difference":
            drop = set(self.selected(rel, v[1]))
            return [c for c in self.selected(rel, v[0]) if c not in drop]
        raise Untranslated(f"Selector {k}")

    def expr(self, rel: Any, e: Any, aggregate: bool = False) -> Any:
        import ibis

        k = _key(e)
        v: Any = e[k] if isinstance(e, dict) else None
        if k == "Column":
            return rel[v]
        if k == "Alias":
            return self.expr(rel, v[0], aggregate)
        if k == "Literal":
            return self.literal(v)
        if k == "Len":
            return rel.count() if aggregate else ibis.literal(None)
        if k == "BinaryExpr":
            op = _BINARY.get(v["op"])
            if op is None:
                raise Untranslated(f"BinaryExpr {v['op']}")
            a = self.expr(rel, v["left"], aggregate)
            b = self.expr(rel, v["right"], aggregate)
            # Ibis reads `x == NULL` (of any type) as `x IS NULL`: a NULL cast
            # to the other side's type keeps the comparison, NULL in Polars.
            if _is_null(v["left"]):
                a = ibis.null().cast(b.type())
            if _is_null(v["right"]):
                b = ibis.null().cast(a.type())
            return op(a, b)
        if k == "Ternary":
            return ibis.ifelse(
                self.expr(rel, v["predicate"], aggregate),
                self.expr(rel, v["truthy"], aggregate),
                self.expr(rel, v["falsy"], aggregate),
            )
        if k == "Cast":
            if v["options"] != "Strict" or _key(v["dtype"]) != "Literal":
                raise Untranslated("Cast that is not strict")
            dtype = v["dtype"]["Literal"]
            to = _DTYPES.get(dtype) if isinstance(dtype, str) else None
            if to is None:
                raise Untranslated(f"Cast to {v['dtype']}")
            return self.expr(rel, v["expr"], aggregate).cast(to)
        if k == "Agg":
            if not aggregate:
                raise Untranslated("an aggregate outside group_by")
            return self.agg(rel, v)
        if k == "Function":
            return self.function(rel, v, aggregate)
        if k == "Over":
            return self.over(rel, v)
        raise Untranslated(k)

    def literal(self, v: Any) -> Any:
        import ibis

        if _is_null({"Literal": v}):
            return ibis.null()
        kind = _key(v)
        inner = v[kind]
        if kind == "Dyn":
            t = _key(inner)
            if inner[t] is None:
                # Polars's JSON writes a NaN or an infinite literal as `null`.
                raise Untranslated("Literal: a non-finite float, which the JSON plan loses")
            if t in ("Int", "Float"):
                return ibis.literal(inner[t])
        if kind == "Scalar":
            t = _key(inner)
            value = inner[t]
            if t == "Null":
                return ibis.null()
            if t == "String":
                return ibis.literal(value, "string")
            if t == "Boolean":
                return ibis.literal(value, "boolean")
            if value is None:
                raise Untranslated("Literal: a non-finite float, which the JSON plan loses")
            if t == "Date":
                return ibis.literal(dt.date(1970, 1, 1) + dt.timedelta(days=value), "date")
            if t in _DTYPES:
                return ibis.literal(value, _DTYPES[t])
        raise Untranslated(f"Literal {str(v)[:40]}")

    def agg(self, rel: Any, v: Any) -> Any:
        k = _key(v)
        a = v[k]
        if k in _AGGS:
            inner = a["input"] if isinstance(a, dict) and "input" in a else a
            if isinstance(a, dict) and a.get("propagate_nans"):
                raise Untranslated(f"Agg {k} propagating NaN")
            return _AGGS[k](self.expr(rel, inner))
        if k == "Count":
            x = self.expr(rel, a["input"])
            return rel.count() if a["include_nulls"] else x.count()
        if k in ("Std", "Var") and a[1] in (0, 1):
            x = self.expr(rel, a[0])
            how = "sample" if a[1] == 1 else "pop"
            return x.std(how=how) if k == "Std" else x.var(how=how)
        raise Untranslated(f"Agg {k}")

    def function(self, rel: Any, v: Any, aggregate: bool) -> Any:
        import ibis

        f = v["function"]
        args = v["input"]
        name = f if isinstance(f, str) else _key(f)
        body = None if isinstance(f, str) else f[name]
        if name in ("Boolean", "StringExpr") and body is not None:
            name, body = (body, None) if isinstance(body, str) else (_key(body), body[_key(body)])
        xs = [self.expr(rel, a, aggregate) for a in args]
        if name in _UNARY and len(xs) == 1 and body is None:
            return _UNARY[name](xs[0])
        if name == "FillNull" and len(xs) == 2:
            return ibis.coalesce(xs[0], xs[1])
        if name == "Coalesce":
            return ibis.coalesce(*xs)
        if name in ("StartsWith", "EndsWith") and len(xs) == 2:
            return xs[0].startswith(xs[1]) if name == "StartsWith" else xs[0].endswith(xs[1])
        raise Untranslated(f"Function {name}")

    def over(self, rel: Any, v: Any) -> Any:
        import ibis

        if v.get("order_by") is not None or v.get("mapping") != "GroupsToRows":
            raise Untranslated("Over with an order or another mapping")
        f = v["function"]
        if _key(f) != "Agg":
            raise Untranslated(f"Over of {_key(f)}")
        by = [self.expr(rel, e) for e in v["partition_by"]]
        return self.agg(rel, f["Agg"]).over(ibis.window(group_by=by))


def translate(plan: Any, con: Any) -> tuple[Any, dict[str, Any]]:
    """`plan` (Polars's DSL, parsed) as an Ibis expression over `con`, and the
    Arrow inputs it put there by name.

    Raises:
        Untranslated: A node the translator does not read.
    """
    t = Translator(con)
    return t.relation(plan), t.inputs


# -- the comparison ----------------------------------------------------------------

_EPOCH = dt.datetime(1970, 1, 1)


def _code(v: Any) -> Any:
    """A value as the checker prints it: dates in days, timestamps and
    durations in microseconds (`core/Sverify/Core/Float.lean`'s codes)."""
    if isinstance(v, dt.datetime):
        if v.tzinfo is not None:
            v = v.astimezone(dt.UTC).replace(tzinfo=None)
        return (v - _EPOCH) // dt.timedelta(microseconds=1)
    if isinstance(v, dt.date):
        return (v - _EPOCH.date()).days
    if isinstance(v, dt.timedelta):
        return v // dt.timedelta(microseconds=1)
    if isinstance(v, list | tuple):
        return tuple(_code(x) for x in v)
    if isinstance(v, dict):
        # A struct, as the checker prints it: its fields' values in order.
        return tuple(_code(x) for x in v.values())
    return v


def _rows(table: Any) -> list[tuple]:
    cols = [table.column(i).to_pylist() for i in range(table.num_columns)]
    return [tuple(_code(c[r]) for c in cols) for r in range(table.num_rows)]


def same(a: Any, b: Any) -> bool:
    """Two values are equal: doubles to the six decimals the checker prints
    (relative to their size), NaN to NaN, the two zeros alike, lists element
    by element."""
    if isinstance(a, list | tuple) or isinstance(b, list | tuple):
        return (
            isinstance(a, list | tuple)
            and isinstance(b, list | tuple)
            and len(a) == len(b)
            and all(same(x, y) for x, y in zip(a, b, strict=True))
        )
    if isinstance(a, float) or isinstance(b, float):
        if a is None or b is None or isinstance(a, bool) or isinstance(b, bool):
            return a is b
        x, y = float(a), float(b)
        if math.isnan(x) or math.isnan(y):
            return math.isnan(x) and math.isnan(y)
        return math.isclose(x, y, rel_tol=1e-6, abs_tol=1e-6)
    return a == b and isinstance(a, bool) == isinstance(b, bool)


def bags_equal(xs: Sequence[tuple], ys: Sequence[tuple]) -> bool:
    """Two results hold the same rows, as bags, values compared by `same`."""
    if len(xs) != len(ys):
        return False
    left = list(ys)
    for x in xs:
        i = next(
            (
                i
                for i, y in enumerate(left)
                if len(x) == len(y) and all(same(a, b) for a, b in zip(x, y, strict=True))
            ),
            None,
        )
        if i is None:
            return False
        left.pop(i)
    return True


def keys_in_order(xs: Sequence[tuple], ys: Sequence[tuple], keys: Sequence[int]) -> bool:
    """Two sorted results have their sort keys in the same order: with the
    bags equal, the rows that tie on the keys may come in any order."""
    return all(all(same(x[k], y[k]) for k in keys) for x, y in zip(xs, ys, strict=True))


def sort_keys(plan: Any, columns: Sequence[str]) -> list[int] | None:
    """The positions of the result's sort keys where the plan's last node is a
    sort (or a slice of one) by plain columns, else None: the result is a bag."""
    if _key(plan) == "Slice":
        plan = plan["Slice"]["input"]
    if _key(plan) != "Sort":
        return None
    out = []
    for e in plan["Sort"]["by_column"]:
        if _key(e) != "Column" or e["Column"] not in columns:
            return None
        out.append(list(columns).index(e["Column"]))
    return out


def replay_collect(plan_text: str, result: Any) -> dict[str, Any]:
    """One captured collect, through the translator and sverify, with its
    outcome (the module's docstring)."""
    import sverify as sv
    from sverify._lean_eval import lean_choices, with_tables

    plan = json.loads(plan_text)
    con = sv.connect()
    try:
        expr, inputs = translate(plan, con)
    except Untranslated as e:
        return {"outcome": "skipped", "reason": f"translator: {normalize(str(e))}"}
    except Exception as e:  # noqa: BLE001 - Ibis refusing the translated expression
        return {"outcome": "skipped", "reason": normalize(f"translator: {type(e).__name__}: {e}")}
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        try:
            report = sv.verify(expr, semantics="polars", on_inferred="warn")
            if report.verdict == sv.Verdict.UNPROVED and report.suggested_requires:
                report = sv.verify(
                    expr, semantics="polars", requires=report.suggested_requires, on_inferred="warn"
                )
        except Exception as e:  # noqa: BLE001 - a construct sverify refuses
            return {"outcome": "refused", "construct": normalize(f"{type(e).__name__}: {e}")}
        if report.verdict == sv.Verdict.UNPROVED:
            first = report.issues[0] if report.issues else None
            why = (first.shown or first.kind) if first else str(report.verdict)
            return {"outcome": "unproved", "reason": normalize(why)}
        assert report.internal_plan is not None
        try:
            rows = {n: [tuple(r.values()) for r in t.to_pylist()] for n, t in inputs.items()}
            choices = lean_choices(json.dumps(with_tables(json.loads(report.internal_plan), rows)))
        except Exception as e:  # noqa: BLE001 - a value the model lacks, or the checker failing
            return {"outcome": "skipped", "reason": normalize(f"lean: {type(e).__name__}: {e}")}
        if choices is None:
            return {"outcome": "skipped", "reason": "lean: the data leaves a choice not listed"}
        try:
            ours = report.run(con, "polars")
        except Exception as e:  # noqa: BLE001 - a refusal or a failed run
            from sverify.errors import PreconditionError, RouteError, UnsupportedError

            if isinstance(e, PreconditionError):
                return {"outcome": "unproved", "reason": normalize(f"data: {e}")}
            if isinstance(e, UnsupportedError | RouteError):
                return {"outcome": "refused", "construct": normalize(f"run: {e}")}
            return {
                "outcome": "disagree",
                "side": "lean",
                "reason": normalize(f"engine raises {type(e).__name__}: {e}"),
            }
    from sverify._lean_eval import allows_rows

    theirs, engine = _rows(result.to_arrow()), _rows(ours)
    keys = sort_keys(plan, result.columns)
    if engine and len(engine[0]) != len(result.columns):
        return {"outcome": "skipped", "reason": "translator: another number of columns"}
    lean_engine = allows_rows(engine, choices, same)
    lean_polars = allows_rows(theirs, choices, same)
    engine_polars = bags_equal(engine, theirs) and (
        keys is None or keys_in_order(engine, theirs, keys)
    )
    if not lean_engine:
        side = "lean" if engine_polars else ("engine" if lean_polars else "neither")
        return {"outcome": "disagree", "side": side, "reason": f"{len(engine)} engine rows"}
    if lean_polars and engine_polars:
        return {"outcome": "agree"}
    return {
        "outcome": "unattributed",
        "reason": f"{len(engine)} rows, Polars {len(theirs)}",
        "plan": hashlib.sha256(plan_text.encode()).hexdigest()[:16],
    }


# -- the plugin ------------------------------------------------------------------

_current: dict[str, Any] = {"test": None, "replays": [], "skip": None}
_busy = [False]


def _wrap(original: Any) -> Any:
    def collect(self: Any, *args: Any, **kwargs: Any) -> Any:
        if _busy[0] or _current["test"] is None:
            return original(self, *args, **kwargs)
        plan_text, skip = None, None
        try:
            # The JSON plan writes each input frame's bytes as a list of numbers:
            # the compact form's size decides first (a large frame filled 8 GB).
            if len(self.serialize()) > MAX_PLAN_BYTES:
                skip = f"inputs: a plan over {MAX_PLAN_BYTES // 1024} KB"
            else:
                with warnings.catch_warnings():
                    warnings.simplefilter("ignore")
                    plan_text = self.serialize(format="json")
        except Exception:  # noqa: BLE001 - a plan Polars cannot serialize
            skip = "translator: no JSON plan"
        try:
            result = original(self, *args, **kwargs)
        except Exception:
            _current["replays"].append({"outcome": "skipped", "reason": "raises"})
            raise
        if _current["skip"] or len(_current["replays"]) >= MAX_COLLECTS:
            return result
        _busy[0] = True
        try:
            if plan_text is None:
                rec = {"outcome": "skipped", "reason": skip or "translator: no JSON plan"}
            elif kwargs.get("background") or not hasattr(result, "to_arrow"):
                rec = {"outcome": "skipped", "reason": "not a frame collected in the foreground"}
            else:
                rec = replay_collect(plan_text, result)
                if (dump := os.environ.get("SVERIFY_POLARS_TESTS_DUMP")) and rec["outcome"] in (
                    "disagree",
                    "unattributed",
                ):
                    # The plan and Polars's result, to triage the collect by hand.
                    stem = Path(dump) / hashlib.sha256(plan_text.encode()).hexdigest()[:16]
                    stem.with_suffix(".json").write_text(plan_text)
                    result.write_parquet(stem.with_suffix(".parquet"))
        except Exception as e:  # noqa: BLE001 - the harness itself
            rec = {"outcome": "skipped", "reason": normalize(f"harness: {type(e).__name__}: {e}")}
        finally:
            _busy[0] = False
        _current["replays"].append(rec)
        return result

    return collect


def pytest_configure(config: Any) -> None:
    import polars as pl

    # Eager frame and series operations go through `_collect_eager`.
    pl.LazyFrame.collect = _wrap(pl.LazyFrame.collect)
    pl.LazyFrame._collect_eager = _wrap(pl.LazyFrame._collect_eager)


def pytest_runtest_setup(item: Any) -> None:
    hypothesis = getattr(getattr(item, "obj", None), "is_hypothesis_test", False)
    _current["test"], _current["replays"] = item.nodeid, []
    _current["skip"] = "a Hypothesis test: its inputs change each run" if hypothesis else None


def pytest_runtest_logreport(report: Any) -> None:
    # Under xdist the controller sees the workers' reports too: only the
    # process that ran the test writes it.
    if _current["test"] != report.nodeid:
        return
    if report.when == "call" or (report.when == "setup" and report.outcome != "passed"):
        passed = report.outcome == "passed" and not hasattr(report, "wasxfail")
        rec = {
            "test": report.nodeid,
            "passed": passed,
            "skip": _current["skip"],
            "replays": list(_current["replays"]),
        }
        with open(os.environ["SVERIFY_POLARS_TESTS_OUT"], "a", encoding="utf-8") as f:
            f.write(json.dumps(rec) + "\n")
        _current["test"] = None


# -- the ledgers -----------------------------------------------------------------


def triage() -> dict[str, dict[str, Any]]:
    """The triaged `unattributed` collects, by test and plan hash
    (`<test>@<plan>`): each `skipped: translation` with its node and reason,
    or the fact or bug it is."""
    return json.loads(TRIAGE.read_text())["triaged"] if TRIAGE.exists() else {}


def classify(rec: dict[str, Any], triaged: dict[str, dict[str, Any]]) -> dict[str, Any]:
    """A test's outcome: its worst collect's, or `skipped`."""
    if not rec["passed"]:
        return {"outcome": "skipped", "reason": "fails, skips or is xfailed in Polars's own run"}
    if rec.get("skip"):
        return {"outcome": "skipped", "reason": rec["skip"]}
    replays = []
    for r in rec["replays"]:
        if r["outcome"] == "unattributed":
            t = triaged.get(f"{rec['test']}@{r['plan']}")
            if t is not None:
                r = {**r, "triaged": t}
                if t["as"] == "skipped: translation":
                    r = {**r, "outcome": "skipped", "reason": f"translation: {t['reason']}"}
        replays.append(r)
    decided = [r for r in replays if r["outcome"] != "skipped"]
    if not decided:
        reasons = sorted({r.get("reason", "") for r in replays})
        return {"outcome": "skipped", "reason": reasons[0] if reasons else "collects nothing"}
    worst = dict(min(decided, key=lambda r: _RANK[r["outcome"]]))
    worst["collects"] = len(rec["replays"])
    return worst


def _module(test: str) -> str:
    """The ledger of a test: its file under `tests/unit/`, `/` as `__`."""
    path = test.split("::")[0].removeprefix("tests/unit/").removesuffix(".py")
    return path.replace("/", "__")


def ledgers(records: Iterable[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    triaged = triage()
    out: dict[str, dict[str, Any]] = {}
    for rec in records:
        test = rec["test"].split("::", 1)[1]
        out.setdefault(_module(rec["test"]), {})[test] = classify(rec, triaged)
    result = {}
    for module, results in sorted(out.items()):
        counts = collections.Counter(r["outcome"] for r in results.values())
        path = module.replace("__", "/")
        result[module] = {
            "polars": TAG,
            "source": f"{REPO}/tree/{TAG}/{TESTS}/unit/{path}.py",
            "license": "MIT",
            "module": module,
            "summary": {k: counts.get(k, 0) for k in OUTCOMES},
            "results": dict(sorted(results.items())),
        }
    return result


def summary(ledger_set: dict[str, dict[str, Any]]) -> dict[str, int]:
    total: collections.Counter[str] = collections.Counter()
    for led in ledger_set.values():
        total.update(led["summary"])
    return {k: total.get(k, 0) for k in OUTCOMES}


README = ROOT / "engines" / "polars" / "facts" / "README.md"
_MARKERS = ("<!-- replay:start -->", "<!-- replay:end -->")


def write_summary(ledger_set: dict[str, dict[str, Any]], readme: Path = README) -> None:
    """The totals and a row per module between `readme`'s `replay` markers."""
    total = summary(ledger_set)
    lines = [
        _MARKERS[0],
        f"Totals over {sum(total.values())} tests of Polars's `{TAG}` suite: "
        + ", ".join(f"{n} {k}" for k, n in total.items())
        + ".",
        "",
        "| Module | " + " | ".join(k.capitalize() for k in OUTCOMES) + " |",
        "|---|" + "---:|" * len(OUTCOMES),
    ]
    for module, led in sorted(ledger_set.items()):
        link = os.path.relpath(LEDGERS / f"{module}.json", readme.parent)
        counts = " | ".join(str(led["summary"][k]) for k in OUTCOMES)
        lines.append(f"| [{module.replace('__', '/')}]({link}) | {counts} |")
    lines.append(_MARKERS[1])
    text = readme.read_text(encoding="utf-8")
    start, end = text.find(_MARKERS[0]), text.find(_MARKERS[1])
    if start < 0 or end < 0:
        raise SystemExit(f"{readme} has no {_MARKERS[0]} … {_MARKERS[1]} block")
    readme.write_text(
        text[:start] + "\n".join(lines) + text[end + len(_MARKERS[1]) :], encoding="utf-8"
    )


def changes(fresh: dict[str, dict[str, Any]]) -> tuple[list[str], list[str]]:
    """How a fresh replay differs from the stored ledgers: what fails the gate
    (a new disagreement, an `unattributed` collect nobody triaged, a test that
    agreed and no longer does), and what only drifted."""
    fails, notes = [], []
    for module, led in fresh.items():
        path = LEDGERS / f"{module}.json"
        old = json.loads(path.read_text())["results"] if path.exists() else {}
        for test, r in led["results"].items():
            was, now = old.get(test, {}).get("outcome"), r["outcome"]
            why = r.get("reason") or r.get("construct", "")
            line = f"{module}::{test}: {was} -> {now} ({why})"
            if now == "unattributed" and "triaged" not in r:
                fails.append(f"{line} [untriaged, plan {r['plan']}]")
            elif was == now:
                continue
            elif now == "disagree" or was == "agree":
                fails.append(line)
            else:
                notes.append(line)
    return fails, notes


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=(__doc__ or "").splitlines()[0])
    ap.add_argument("modules", nargs="*", default=list(MODULES))
    ap.add_argument("--write", action="store_true", help="rewrite the ledgers")
    ap.add_argument("--check", action="store_true", help="compare with the ledgers")
    ap.add_argument("--summary", action="store_true", help="the stored ledgers' totals")
    ap.add_argument("-n", "--workers", type=int, default=2)
    ap.add_argument("--save", type=Path, help="append the replay's records (JSONL) here")
    ap.add_argument("--load", type=Path, help="read the records a --save wrote, not replaying")
    args = ap.parse_args(argv)
    if args.summary:
        stored = {
            p.stem: json.loads(p.read_text()) for p in sorted(LEDGERS.glob("*.json")) if p != TRIAGE
        }
        print(json.dumps(summary(stored)))
        return 0
    if args.load:
        records = [json.loads(line) for line in args.load.read_text().splitlines() if line]
    else:
        records = replay(args.modules, args.workers, args.save)
    fresh = ledgers(records)
    print(json.dumps(summary(fresh)))
    for module, led in fresh.items():
        print(f"{module}: {json.dumps(led['summary'])}")
    fails, notes = changes(fresh)
    if args.write:
        LEDGERS.mkdir(parents=True, exist_ok=True)
        for module, led in fresh.items():
            text = json.dumps(led, indent=2, ensure_ascii=False) + "\n"
            (LEDGERS / f"{module}.json").write_text(text)
        stored = {
            p.stem: json.loads(p.read_text()) for p in sorted(LEDGERS.glob("*.json")) if p != TRIAGE
        }
        write_summary(stored)
    if notes:
        print(f"{len(notes)} change(s) the ledgers take when rewritten:")
        print("\n".join(f"  {n}" for n in notes[:20]))
    if fails:
        print(f"{len(fails)} finding(s):", file=sys.stderr)
        print("\n".join(fails[:50]), file=sys.stderr)
        if args.check:
            return 1
    return 0


if __name__ == "__main__":
    with contextlib.suppress(KeyboardInterrupt):
        raise SystemExit(main())

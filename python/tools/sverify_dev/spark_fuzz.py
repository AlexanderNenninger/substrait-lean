# ruff: noqa: E501 - targets are SQL strings and value tables, one per line
"""Fuzz the open deviations of Spark's facts (#738, #739).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API. The Spark counterpart of `sverify_dev.duckdb_fuzz`.

Each `Target` is one open deviation of `characterization/spark/facts/`: a
construct in Spark's SQL, a generator of random rows that leans on the edges
the fact names (bounds, zeros, NaN, ±inf, NULL), and a model of what the fact
says Spark gives, per ANSI setting. Every row runs on a local Spark session
with `spark.sql.ansi.enabled` on and off, and on Spark's two paths for a small
table (folded: the optimizer evaluates the query on the driver; codegen:
`ConvertToLocalRelation` and `ConstantFolding` excluded, so the query runs as
a job with whole-stage code generation), as `sverify_dev.probe_spark` does.

- A row whose Spark result (its value, its type, or its error class) differs
  from the model is a finding: Spark does something the fact does not say.
- Where the target has a DuckDB-SQL form, `Rel.eval` evaluates it on the
  same rows (sverify's lift, the reference profile), and the run counts the
  rows where Spark's value differs from the reference: the deviation's
  footprint. `Rel.eval` gives values; where the reference raises, `verify`
  flags the plan, so a row Spark raises on is not compared.

Rows the model predicts to raise run one by one (a sample of them); the
others run as one query, and an unexpected raise is narrowed down to its row.

`python -m sverify_dev.spark_fuzz [targets…] --rows N --seed S` runs the
targets and writes `characterization/spark/fuzz.json`: per target, the fact,
the seed, the rows and settings, the counts and the findings. It needs
`pyspark` and a JVM; run it on homelab (CLAUDE.md), with one Spark session.
"""

from __future__ import annotations

import argparse
import copy
import datetime as dt
import json
import logging
import math
import random
import re
import struct
import sys
import time
from collections import Counter
from collections.abc import Callable, Sequence
from dataclasses import dataclass, field
from decimal import ROUND_HALF_EVEN, ROUND_HALF_UP, Context, Decimal
from pathlib import Path
from typing import Any

import numpy as np

_HERE = Path(__file__).resolve()
OUT = _HERE.parents[3] / "characterization" / "spark" / "fuzz.json"

#: The session: `sverify_dev.probe_spark.BASE_CONF`.
CONF: dict[str, str] = {
    "spark.master": "local[2]",
    "spark.driver.memory": "2g",
    "spark.ui.enabled": "false",
    "spark.ui.showConsoleProgress": "false",
    "spark.sql.shuffle.partitions": "2",
    "spark.sql.session.timeZone": "UTC",
    "spark.sql.timestampType": "TIMESTAMP_NTZ",
    "spark.sql.caseSensitive": "true",
    "spark.sql.parser.escapedStringLiterals": "false",
    "spark.sql.execution.arrow.pyspark.enabled": "false",
}
CODEGEN_EXCLUDED = (
    "org.apache.spark.sql.catalyst.optimizer.ConvertToLocalRelation,"
    "org.apache.spark.sql.catalyst.optimizer.ConstantFolding"
)
PATHS = ("folded", "codegen")


@dataclass(frozen=True)
class Raise:
    """An error, by error class (or the Java exception's class)."""

    cls: str

    def __str__(self) -> str:
        return f"raise {self.cls}"


NULL = None
I8, I16, I32, I64 = (2**7, 2**15, 2**31, 2**63)


@dataclass
class Expr:
    """One construct of a target: its Spark SQL over the table `t`, the
    model of the fact (`row, ansi -> value | Raise`), the result type Spark
    should give (by ANSI setting, `None` to skip), and a DuckDB form for
    `Rel.eval` with its comparison."""

    name: str
    spark: str
    model: Callable[[tuple, bool], Any]
    type: str | Callable[[bool], str] | None = None
    duckdb: str | None = None
    same: Callable[[Any, Any], bool] | None = None
    """How Spark's value is compared with the model's (exact by default)."""


@dataclass
class Target:
    fact: str
    columns: str
    """The table's columns, as Spark DDL (`a TINYINT, b TINYINT`)."""
    rows: Callable[[random.Random], tuple]
    exprs: list[Expr]
    ibis: dict[str, str] | None = None
    """The columns' Ibis types, for the DuckDB forms."""
    conf: list[dict[str, str]] = field(default_factory=lambda: [{}])
    """Extra settings, each run as its own pass."""
    group: bool = False
    """The constructs are aggregates: rows carry a group key `g` first."""
    note: str = ""


# --- Values -----------------------------------------------------------------


def pick(
    r: random.Random, edges: Sequence[Any], rand: Callable[[random.Random], Any], p: float = 0.5
) -> Any:
    return r.choice(edges) if r.random() < p else rand(r)


def wrap(x: int, bits: int) -> int:
    m = 1 << bits
    x %= m
    return x - m if x >= m >> 1 else x


def fits(x: int, bits: int) -> bool:
    return -(1 << (bits - 1)) <= x < 1 << (bits - 1)


def tdiv(a: int, b: int) -> int:
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b >= 0) else -q


def tmod(a: int, b: int) -> int:
    return a - b * tdiv(a, b)


def bits(x: float) -> int:
    return struct.unpack("<q", struct.pack("<d", x))[0]


def neg_nan() -> float:
    return struct.unpack("<d", struct.pack("<Q", 0xFFF8000000000000))[0]


def same_double(a: Any, b: Any) -> bool:
    """Equal doubles, zero signs included; any NaN equals any NaN (the NaN's
    sign is spark-nan-sign's and the platform's)."""
    if a is None or b is None or isinstance(a, Raise) or isinstance(b, Raise):
        return a == b
    if math.isnan(a) or math.isnan(b):
        return math.isnan(a) and math.isnan(b)
    return a == b and math.copysign(1, a) == math.copysign(1, b)


def same_bits(a: Any, b: Any) -> bool:
    if isinstance(a, float) and isinstance(b, float):
        return bits(a) == bits(b)
    return a == b


def ulps(a: float, b: float) -> int:
    if math.isnan(a) or math.isnan(b):
        return 0 if math.isnan(a) and math.isnan(b) else 1 << 62
    if math.isinf(a) or math.isinf(b):
        return 0 if a == b else 1 << 62

    def key(x: float) -> int:
        i = bits(x)
        return i if i >= 0 else -(i & 0x7FFFFFFFFFFFFFFF)

    return abs(key(a) - key(b))


def within_ulp(n: int) -> Callable[[Any, Any], bool]:
    def same(a: Any, b: Any) -> bool:
        if not isinstance(a, float) or not isinstance(b, float):
            return a == b
        return ulps(a, b) <= n

    return same


def close(rel: float) -> Callable[[Any, Any], bool]:
    def same(a: Any, b: Any) -> bool:
        if not isinstance(a, float) or not isinstance(b, float):
            return a == b
        if math.isnan(a) or math.isnan(b) or math.isinf(a) or math.isinf(b):
            return same_double(a, b) or (a == b)
        return abs(a - b) <= rel * max(abs(a), abs(b), 1e-300) or a == b

    return same


def nd(f: Callable[..., Any], *xs: float) -> float:
    """A numpy float function with IEEE results and no warnings."""
    with np.errstate(all="ignore"):
        return float(f(*(np.float64(x) for x in xs)))


INT_EDGES = {
    "TINYINT": [-(I8), I8 - 1, 0, 1, -1, 2, -2, 7, -7],
    "SMALLINT": [-(I16), I16 - 1, 0, 1, -1, 2, -2, 7, -7],
    "INT": [-(I32), I32 - 1, 0, 1, -1, 2, -2, 7, -7],
    "BIGINT": [-(I64), I64 - 1, 0, 1, -1, 2, -2, 7, -7, 3037000500],
}
WIDTH = {"TINYINT": 8, "SMALLINT": 16, "INT": 32, "BIGINT": 64}

DOUBLE_EDGES = [0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 2.5, -2.5, math.inf, -math.inf, math.nan,
                1e308, -1e308, 5e-324, 0.1, 2.675, 1e16, 1e20, -1e20, 2.0**63, -(2.0**63)]  # fmt: skip


def rand_int(bits_: int) -> Callable[[random.Random], int]:
    def gen(r: random.Random) -> int:
        k = r.choice([4, 8, bits_ - 1, bits_ - 1])
        k = min(k, bits_ - 1)
        return r.randint(-(1 << k), (1 << k) - 1)

    return gen


def rand_double(r: random.Random) -> float:
    c = r.random()
    if c < 0.3:
        return r.uniform(-10, 10)
    if c < 0.5:
        return round(r.uniform(-1000, 1000), r.randint(0, 3))
    if c < 0.7:
        return r.choice([-1, 1]) * 10 ** r.uniform(-30, 30)
    if c < 0.85:
        return float(r.randint(-100, 100)) / 8
    return struct.unpack("<d", struct.pack("<Q", r.getrandbits(64)))[0]


def dbl(r: random.Random, p: float = 0.4) -> float | None:
    if r.random() < 0.05:
        return None
    return pick(r, DOUBLE_EDGES, rand_double, p)


# --- Targets: integers ------------------------------------------------------


def _int_divide() -> list[Target]:
    found = []
    for t, w in WIDTH.items():

        def rows(r: random.Random, t: str = t, w: int = w) -> tuple:
            def v() -> int | None:
                return None if r.random() < 0.05 else pick(r, INT_EDGES[t], rand_int(w))

            return (v(), v())

        def div(row: tuple, ansi: bool, w: int = w) -> Any:
            a, b = row
            if a is None or b is None:
                return None
            if b == 0:
                return Raise("DIVIDE_BY_ZERO") if ansi else None
            q = tdiv(a, b)
            if not fits(q, 64):
                return Raise("ARITHMETIC_OVERFLOW") if ansi else wrap(q, 64)
            return q

        def slash(row: tuple, ansi: bool) -> Any:
            a, b = row
            if a is None or b is None:
                return None
            if b == 0:
                return Raise("DIVIDE_BY_ZERO") if ansi else None
            return float(a) / float(b)

        ibis_t = {8: "int8", 16: "int16", 32: "int32", 64: "int64"}[w]
        found.append(
            Target(
                "spark-int-divide",
                f"a {t}, b {t}",
                rows,
                [
                    Expr(f"{t.lower()} div", "a div b", div, "bigint", "a // b"),
                    Expr(f"{t.lower()} /", "a / b", slash, "double", None, same_double),
                ],
                ibis={"a": ibis_t, "b": ibis_t},
            )
        )
    return found


def _java_shift(op: str, a: int, n: int, w: int) -> int:
    n &= w - 1
    if op == "<<":
        return wrap(a << n, w)
    if op == ">>":
        return a >> n
    return (a % (1 << w)) >> n if n else a


def _int_shift() -> list[Target]:
    found = []
    for t in ("TINYINT", "SMALLINT", "INT", "BIGINT"):
        w = 64 if t == "BIGINT" else 32

        def rows(r: random.Random, t: str = t) -> tuple:
            a = None if r.random() < 0.05 else pick(r, INT_EDGES[t], rand_int(WIDTH[t]))
            n = (
                None
                if r.random() < 0.05
                else pick(
                    r, [0, 1, -1, 31, 32, 33, 63, 64, 65, -33, -65], lambda r: r.randint(-200, 200)
                )
            )
            return (a, n)

        def model(op: str, w: int = w) -> Callable[[tuple, bool], Any]:
            def f(row: tuple, ansi: bool) -> Any:
                a, n = row
                return None if a is None or n is None else _java_shift(op, a, n, w)

            return f

        rt = "bigint" if t == "BIGINT" else "int"
        found.append(
            Target(
                "spark-int-shift",
                f"a {t}, n INT",
                rows,
                [
                    Expr(f"{t.lower()} shiftleft", "shiftleft(a, n)", model("<<"), rt),
                    Expr(f"{t.lower()} shiftright", "shiftright(a, n)", model(">>"), rt),
                    Expr(
                        f"{t.lower()} shiftrightunsigned",
                        "shiftrightunsigned(a, n)",
                        model(">>>"),
                        rt,
                    ),
                ],
            )
        )
    return found


def _pow(a: float, b: float) -> float:
    return nd(np.power, a, b)


def _int_pow() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        a = (
            None
            if r.random() < 0.05
            else pick(r, INT_EDGES["BIGINT"] + [3, -3, 10], lambda r: r.randint(-20, 20))
        )
        b = (
            None
            if r.random() < 0.05
            else pick(r, [0, 1, -1, 2, 63, 64, 1024, -1024, -2], lambda r: r.randint(-70, 70))
        )
        return (a, b)

    def model(row: tuple, ansi: bool) -> Any:
        a, b = row
        return None if a is None or b is None else _pow(float(a), float(b))

    return [
        Target(
            "spark-int-pow",
            "a BIGINT, b BIGINT",
            rows,
            [Expr("bigint power", "power(a, b)", model, "double", "power(a, b)", within_ulp(1))],
            ibis={"a": "int64", "b": "int64"},
            note="Spark calls StrictMath.pow (fdlibm), the model numpy's pow: compared within 1 ulp.",
        )
    ]


# --- Targets: decimals ------------------------------------------------------

_D34 = Context(prec=34, rounding=ROUND_HALF_UP)


def _rand_dec(r: random.Random, s: int) -> Decimal:
    digits = r.choice([1, 5, 20, 33, 34, 35, 36, 37, 38, 38, 38])
    n = r.randint(10 ** (digits - 1) if digits > 1 else 0, 10**digits - 1)
    if r.random() < 0.3:
        n = int(str(n)[:-1] + "5") if digits > 1 else 5
    if r.random() < 0.1:
        n = 10**38 - 1
    return Decimal(-n if r.random() < 0.5 else n).scaleb(-s)


def _decimal_negate() -> list[Target]:
    found = []
    for s in (0, 10):

        def rows(r: random.Random, s: int = s) -> tuple:
            return (None if r.random() < 0.03 else _rand_dec(r, s),)

        def model(f: Callable[[Decimal], Decimal], s: int = s) -> Callable[[tuple, bool], Any]:
            def m(row: tuple, ansi: bool) -> Any:
                (x,) = row
                if x is None:
                    return None
                y = _D34.plus(f(x))
                if abs(y) >= Decimal(10) ** (38 - s):
                    return Raise("NUMERIC_VALUE_OUT_OF_RANGE")
                return y.quantize(Decimal(1).scaleb(-s), context=Context(prec=100))

            return m

        found.append(
            Target(
                "spark-decimal-negate",
                f"x DECIMAL(38,{s})",
                rows,
                [
                    Expr(
                        f"-x decimal(38,{s})", "-x", model(lambda x: -x), f"decimal(38,{s})", "-x"
                    ),
                    Expr(
                        f"abs decimal(38,{s})", "abs(x)", model(abs), f"decimal(38,{s})", "abs(x)"
                    ),
                    Expr(
                        f"0 - x decimal(38,{s})",
                        "0 - x",
                        lambda row, ansi: None if row[0] is None else -row[0],
                        None,
                    ),
                ],
                ibis={"x": f"decimal(38,{s})"},
                note="The model rounds to 34 significant digits half up (MathContext.DECIMAL128 as the fact states).",
            )
        )
    return found


def _size_limits() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        d = r.choice([30, 36, 37, 38, 38, 39, 40])
        n = r.randint(10 ** (d - 1), 10**d - 1)
        s = r.choice([0, 0, 2, 10])
        return (("-" if r.random() < 0.5 else "") + str(Decimal(n).scaleb(-s)), s)

    def model(row: tuple, ansi: bool) -> Any:
        x, s = row
        v = Decimal(x)
        # CAST(x AS DECIMAL(38, 2)): rounds half up to 2 places, then fits 38 digits or not.
        y = v.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP, context=Context(prec=100))
        if abs(y) >= Decimal(10) ** 36:
            return Raise("NUMERIC_VALUE_OUT_OF_RANGE") if ansi else None
        return y

    return [
        Target(
            "spark-exec-size-limits",
            "x STRING, s INT",
            rows,
            [Expr("cast to decimal(38,2)", "CAST(x AS DECIMAL(38,2))", model, "decimal(38,2)")],
            note="Decimal text of 30 to 40 digits cast to DECIMAL(38,2).",
        )
    ]


# --- Targets: doubles -------------------------------------------------------


def _two_doubles(r: random.Random) -> tuple:
    return (dbl(r), dbl(r))


def _ieee(f: Callable[..., float]) -> Callable[[tuple, bool], Any]:
    def m(row: tuple, ansi: bool) -> Any:
        return None if any(x is None for x in row) else nd(f, *row)

    return m


def _double_arith() -> list[Target]:
    return [
        Target(
            "spark-double-arith",
            "a DOUBLE, b DOUBLE",
            _two_doubles,
            [
                Expr("+", "a + b", _ieee(np.add), "double", "a + b", same_double),
                Expr("-", "a - b", _ieee(np.subtract), "double", "a - b", same_double),
                Expr("*", "a * b", _ieee(np.multiply), "double", "a * b", same_double),
            ],
            ibis={"a": "float64", "b": "float64"},
        )
    ]


def _zero_divisor(f: Callable[..., float], cls: str) -> Callable[[tuple, bool], Any]:
    def m(row: tuple, ansi: bool) -> Any:
        a, b = row
        if a is None or b is None:
            return None
        if b == 0:
            return Raise(cls) if ansi else None
        return nd(f, a, b)

    return m


def _pmod(row: tuple, ansi: bool) -> Any:
    """`pmod` as the fact states it: `((a % b) + b) % b`."""
    a, b = row
    if a is None or b is None:
        return None
    if b == 0:
        return Raise("REMAINDER_BY_ZERO") if ansi else None
    return nd(np.fmod, nd(np.fmod, a, b) + b, b)


def _double_divide_mod() -> list[Target]:
    return [
        Target(
            "spark-double-divide",
            "a DOUBLE, b DOUBLE",
            _two_doubles,
            [
                Expr(
                    "/",
                    "a / b",
                    _zero_divisor(np.divide, "DIVIDE_BY_ZERO"),
                    "double",
                    "a / b",
                    same_double,
                )
            ],
            ibis={"a": "float64", "b": "float64"},
        ),
        Target(
            "spark-double-modulus",
            "a DOUBLE, b DOUBLE",
            _two_doubles,
            [
                Expr(
                    "%",
                    "a % b",
                    _zero_divisor(np.fmod, "REMAINDER_BY_ZERO"),
                    "double",
                    "fmod(a, b)",
                    same_double,
                ),
                Expr("pmod", "pmod(a, b)", _pmod, "double", None, same_double),
            ],
            ibis={"a": "float64", "b": "float64"},
        ),
    ]


def _one_double(r: random.Random) -> tuple:
    return (dbl(r, 0.5),)


def _elem(
    f: Callable[[float], float], domain: Callable[[float], bool] | None = None
) -> Callable[[tuple, bool], Any]:
    def m(row: tuple, ansi: bool) -> Any:
        (x,) = row
        if x is None:
            return None
        if domain is not None and not domain(x):
            return None
        return nd(f, x)

    return m


def _elem_rounding() -> list[Target]:
    def pos(x: float) -> bool:
        return x > 0

    def log2(x: float) -> float:
        return nd(np.log, x) / math.log(2) if x > 0 else math.nan

    def ln_rows(r: random.Random) -> tuple:
        x = dbl(r, 0.3)
        return (abs(x) if x is not None and r.random() < 0.8 else x,)

    return [
        Target(
            "spark-elem-rounding",
            "x DOUBLE",
            _one_double,
            [
                Expr("exp", "exp(x)", _elem(np.exp), "double", "exp(x)", within_ulp(1)),
                Expr("sqrt", "sqrt(x)", _elem(np.sqrt), "double", None, same_double),
                Expr("sin", "sin(x)", _elem(np.sin), "double", "sin(x)", within_ulp(1)),
                Expr("cos", "cos(x)", _elem(np.cos), "double", "cos(x)", within_ulp(1)),
                Expr("tan", "tan(x)", _elem(np.tan), "double", "tan(x)", within_ulp(1)),
                Expr("atan", "atan(x)", _elem(np.arctan), "double", "atan(x)", within_ulp(1)),
                Expr("cbrt", "cbrt(x)", _elem(np.cbrt), "double", "cbrt(x)", within_ulp(1)),
            ],
            ibis={"x": "float64"},
            note="Model: numpy (the C library); the fact allows 1 ulp for java.lang.Math and none for sqrt.",
        ),
        Target(
            "spark-elem-rounding",
            "x DOUBLE",
            ln_rows,
            [
                Expr("ln", "ln(x)", _elem(np.log, pos), "double", None, within_ulp(1)),
                Expr("log10", "log10(x)", _elem(np.log10, pos), "double", None, within_ulp(1)),
                Expr("log2", "log2(x)", _elem(log2, pos), "double", None, within_ulp(1)),
            ],
            note="log2 modelled as ln(x) / ln(2), two roundings, as the fact states.",
        ),
    ]


def _math_domain() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        e = [0.0, -0.0, 1.0, -1.0, 2.5, -2.5, math.inf, -math.inf, math.nan, -8.0, 1 / 3]
        return (pick(r, e, rand_double, 0.6), pick(r, e, rand_double, 0.6))

    def le0(x: float) -> bool:
        return not (x <= 0)

    def log_b(row: tuple, ansi: bool) -> Any:
        b, x = row
        if b <= 0 or x <= 0:
            return None
        return nd(np.divide, nd(np.log, x), nd(np.log, b))

    def atan2(row: tuple, ansi: bool) -> Any:
        y, x = row
        return nd(np.arctan2, y + 0.0, x + 0.0)

    return [
        Target(
            "spark-math-domain",
            "a DOUBLE, b DOUBLE",
            rows,
            [
                Expr(
                    "sqrt",
                    "sqrt(a)",
                    lambda row, ansi: nd(np.sqrt, row[0]),
                    "double",
                    None,
                    same_double,
                ),
                Expr(
                    "asin",
                    "asin(a)",
                    lambda row, ansi: nd(np.arcsin, row[0]),
                    "double",
                    None,
                    within_ulp(1),
                ),
                Expr(
                    "acos",
                    "acos(a)",
                    lambda row, ansi: nd(np.arccos, row[0]),
                    "double",
                    None,
                    within_ulp(1),
                ),
                Expr(
                    "ln",
                    "ln(a)",
                    lambda row, ansi: _elem(np.log, le0)((row[0],), ansi),
                    "double",
                    None,
                    within_ulp(1),
                ),
                Expr(
                    "log10",
                    "log10(a)",
                    lambda row, ansi: _elem(np.log10, le0)((row[0],), ansi),
                    "double",
                    None,
                    within_ulp(1),
                ),
                Expr("log", "log(a, b)", log_b, "double", None, within_ulp(1)),
                Expr(
                    "power",
                    "power(a, b)",
                    lambda row, ansi: _pow(*row),
                    "double",
                    None,
                    within_ulp(1),
                ),
                Expr("atan2", "atan2(a, b)", atan2, "double", None, within_ulp(1)),
                Expr(
                    "sin",
                    "sin(a)",
                    lambda row, ansi: nd(np.sin, row[0]),
                    "double",
                    None,
                    within_ulp(1),
                ),
            ],
            note="NaN and the signs of zero in the model are IEEE's; logs NULL for x <= 0; atan2 adds 0.0 to both arguments.",
        )
    ]


def _nan_sign() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        return (
            r.choice([math.nan, neg_nan(), 1.0, -0.0, math.inf]),
            r.choice([math.inf, -math.inf, 0.0, 1.0]),
        )

    def flip(x: float) -> float:
        return struct.unpack(
            "<d", struct.pack("<Q", struct.unpack("<Q", struct.pack("<d", x))[0] ^ (1 << 63))
        )[0]

    def created(row: tuple, ansi: bool) -> Any:
        a, b = row
        v = nd(np.subtract, b, b)  # inf - inf is NaN, else 0
        return neg_nan() if math.isnan(v) else v

    return [
        Target(
            "spark-nan-sign",
            "a DOUBLE, b DOUBLE",
            rows,
            [
                Expr("-x", "-a", lambda row, ansi: flip(row[0]), "double", None, same_bits),
                Expr("abs", "abs(a)", lambda row, ansi: abs(row[0]), "double", None, same_bits),
                Expr(
                    "x * -1",
                    "a * -1.0D",
                    lambda row, ansi: (
                        neg_nan()
                        if math.isnan(row[0]) and math.copysign(1, row[0]) < 0
                        else (math.nan if math.isnan(row[0]) else row[0] * -1.0)
                    ),
                    "double",
                    None,
                    same_bits,
                ),
                Expr("b - b", "b - b", created, "double", None, same_bits),
            ],
            note="Bit for bit; the created NaN modelled negative, as on x86-64 (spark-exec-platform).",
        )
    ]


def _zero_sign() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        z = [0.0, -0.0, 1.0, -1.0, 5e-324, -5e-324]
        return (r.choice(z), r.choice(z))

    def java_str(x: float) -> str:
        return _java_double(x)

    return [
        Target(
            "spark-zero-sign",
            "a DOUBLE, b DOUBLE",
            rows,
            [
                Expr("+", "a + b", _ieee(np.add), "double", None, same_bits),
                Expr("*", "a * b", _ieee(np.multiply), "double", None, same_bits),
                Expr(
                    "/",
                    "a / b",
                    _zero_divisor(np.divide, "DIVIDE_BY_ZERO"),
                    "double",
                    None,
                    same_bits,
                ),
                Expr("-x", "-a", lambda row, ansi: -row[0], "double", None, same_bits),
                Expr("abs", "abs(a)", lambda row, ansi: abs(row[0]), "double", None, same_bits),
                Expr(
                    "cast string", "CAST(a AS STRING)", lambda row, ansi: java_str(row[0]), "string"
                ),
            ],
        )
    ]


def _zero_order() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        return (r.randint(0, 40), r.choice([0.0, -0.0, 0.0, -0.0, 1.0, None]))

    def first(vals: list) -> Any:
        xs = [x for x in vals if x is not None]
        return xs or None

    def minmax(f: Callable) -> Callable[[list, bool], Any]:
        def m(vals: list, ansi: bool) -> Any:
            xs = [x for x in vals if x is not None]
            if not xs:
                return None
            best = f(xs)
            return [x for x in xs if x == best]

        return m

    return [
        Target(
            "spark-zero-order",
            "g INT, x DOUBLE",
            rows,
            [
                Expr("min", "min(x)", minmax(min), "double", None, _one_of_zeros),
                Expr("max", "max(x)", minmax(max), "double", None, _one_of_zeros),
                Expr(
                    "group key",
                    "first(x) = 0.0 AND count(*) > 0",
                    lambda vals, ansi: None if first(vals) is None else first(vals)[0] == 0.0,
                    "boolean",
                ),
            ],
            group=True,
            note="min and max may return any of the equal zeros they saw, by task order; checked that the zero is one of the group's.",
        ),
        Target(
            "spark-zero-order",
            "a DOUBLE, b DOUBLE",
            lambda r: (r.choice([0.0, -0.0, 1.0]), r.choice([0.0, -0.0, 1.0])),
            [
                Expr("=", "a = b", lambda row, ansi: row[0] == row[1], "boolean"),
                Expr("<", "a < b", lambda row, ansi: row[0] < row[1], "boolean"),
                Expr("<=>", "a <=> b", lambda row, ansi: row[0] == row[1], "boolean"),
                Expr(
                    "greatest",
                    "greatest(a, b)",
                    lambda row, ansi: [row[0]] if row[0] >= row[1] else [row[1]],
                    "double",
                    None,
                    _one_of_zeros,
                ),
            ],
        ),
    ]


def _one_of_zeros(got: Any, allowed: Any) -> bool:
    if allowed is None or got is None:
        return got is allowed
    return any(same_bits(got, a) for a in allowed)


def _java_double(x: float) -> str:
    """`Double.toString` (JDK 19 and later: the shortest decimal)."""
    if math.isnan(x):
        return "NaN"
    if math.isinf(x):
        return "Infinity" if x > 0 else "-Infinity"
    if x == 0:
        return "-0.0" if math.copysign(1, x) < 0 else "0.0"
    r = repr(x)
    sign = "-" if r.startswith("-") else ""
    r = r.lstrip("-")
    m, _, e = r.partition("e")
    exp = int(e) if e else 0
    ip, _, fp = m.partition(".")
    digits = (ip + fp).lstrip("0")
    point = len(ip) + exp  # the decimal point after this many digits of ip+fp
    lead = len(ip + fp) - len((ip + fp).lstrip("0"))
    point -= lead
    digits = digits.rstrip("0") or "0"
    if 1e-3 <= abs(x) < 1e7:
        if point <= 0:
            return f"{sign}0.{'0' * -point}{digits}"
        if point >= len(digits):
            return f"{sign}{digits}{'0' * (point - len(digits))}.0"
        return f"{sign}{digits[:point]}.{digits[point:]}"
    if len(digits) == 1:
        # At least two digits: the two-digit decimal nearest the value
        # (`Double.MIN_VALUE` prints as 4.9E-324, 1e20 as 1.0E20).
        m2, _, e2 = f"{Decimal(abs(x)):.1e}".partition("e")
        return f"{sign}{m2}E{int(e2)}"
    return f"{sign}{digits[0]}.{digits[1:]}E{point - 1}"


def _round() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        x = dbl(r, 0.4)
        if x is not None and r.random() < 0.4:
            x = round(r.uniform(-1000, 1000), r.randint(1, 4))
            if r.random() < 0.5:
                x = float(f"{int(x)}.{r.randint(0, 99):02d}5")
        return (x,)

    def rnd(d: int, mode: str) -> Callable[[tuple, bool], Any]:
        def m(row: tuple, ansi: bool) -> Any:
            (x,) = row
            if x is None:
                return None
            if math.isnan(x) or math.isinf(x):
                return x
            v = Decimal(_java_double(x).replace("E", "e"))
            y = v.quantize(Decimal(1).scaleb(-d), rounding=mode, context=Context(prec=400))
            return float(y) + 0.0

        return m

    def floor_ceil(f: Callable[[float], float]) -> Callable[[tuple, bool], Any]:
        def m(row: tuple, ansi: bool) -> Any:
            (x,) = row
            if x is None:
                return None
            if math.isnan(x):
                return 0
            if math.isinf(x):
                if ansi:
                    return Raise("ARITHMETIC_OVERFLOW")
                return I64 - 1 if x > 0 else -I64
            y = int(f(x))
            if not fits(y, 64):
                if ansi:
                    return Raise("ARITHMETIC_OVERFLOW")
                return I64 - 1 if y > 0 else -I64
            return y

        return m

    exprs = []
    for d in (0, 1, 2, -2):
        exprs.append(
            Expr(
                f"round(x, {d})",
                f"round(x, {d})",
                rnd(d, ROUND_HALF_UP),
                "double",
                f"round(x, {d})",
                same_double,
            )
        )
        exprs.append(
            Expr(
                f"bround(x, {d})",
                f"bround(x, {d})",
                rnd(d, ROUND_HALF_EVEN),
                "double",
                None,
                same_double,
            )
        )
    exprs.append(Expr("floor", "floor(x)", floor_ceil(math.floor), "bigint"))
    exprs.append(Expr("ceil", "ceil(x)", floor_ceil(math.ceil), "bigint"))
    return [Target("spark-round", "x DOUBLE", rows, exprs, ibis={"x": "float64"},
                   note="round and bround on the shortest decimal text (Double.toString), HALF_UP and HALF_EVEN.")]  # fmt: skip


def _fp32() -> list[Target]:
    f32 = np.float32

    def rows(r: random.Random) -> tuple:
        e = [0.1, 0.2, 16777216.0, 1.0, -1.0, 3e38, -3e38, 0.0, -0.0, math.inf, math.nan, 1e-45]

        def f() -> float:
            with np.errstate(all="ignore"):
                return float(f32(pick(r, e, rand_double, 0.4)))

        return (
            f(),
            f(),
            r.randint(-(2**31), 2**31 - 1) if r.random() < 0.5 else r.randint(-100, 100),
        )

    def op(fn: Callable) -> Callable[[tuple, bool], Any]:
        def m(row: tuple, ansi: bool) -> Any:
            with np.errstate(all="ignore"):
                return float(fn(f32(row[0]), f32(row[1])))

        return m

    def plus_int(row: tuple, ansi: bool) -> Any:
        a, _, i = row
        with np.errstate(all="ignore"):
            return float(np.float64(a) + np.float64(i)) if ansi else float(f32(a) + f32(i))

    def div(row: tuple, ansi: bool) -> Any:
        a, b, _ = row
        if b == 0:
            return Raise("DIVIDE_BY_ZERO") if ansi else None
        return nd(np.divide, a, b)

    return [
        Target(
            "spark-fp32",
            "a FLOAT, b FLOAT, i INT",
            rows,
            [
                Expr("float +", "a + b", op(np.add), "float", None, same_double),
                Expr("float *", "a * b", op(np.multiply), "float", None, same_double),
                Expr("float /", "a / b", div, "double", None, same_double),
                Expr(
                    "float + int",
                    "a + i",
                    plus_int,
                    lambda ansi: "double" if ansi else "float",
                    None,
                    same_double,
                ),
                Expr(
                    "sqrt float",
                    "sqrt(a)",
                    lambda row, ansi: nd(np.sqrt, row[0]),
                    "double",
                    None,
                    same_double,
                ),
            ],
            note="`a / b` of two FLOATs divides in DOUBLE (Spark's `Divide` casts both sides).",
        )
    ]


# --- Targets: strings, casts, lists, dates -----------------------------------

_CHARS = "aé😀 Zß\t"


def _rand_str(r: random.Random) -> str | None:
    if r.random() < 0.05:
        return None
    return "".join(r.choice(_CHARS) for _ in range(r.randint(0, 7)))


def _substr_model(s: str | None, pos: int | None, ln: int | None) -> Any:
    if s is None or pos is None or ln is None:
        return None
    n = len(s)
    start = pos - 1 if pos > 0 else (n + pos if pos < 0 else 0)
    end = start + ln
    end = max(min(end, 2**31 - 1), -(2**31))
    start = max(start, 0)
    return "" if start >= end else s[start:end]


def _substring() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        return (_rand_str(r), r.randint(-10, 10), r.randint(-2, 10))

    return [
        Target(
            "spark-substring",
            "s STRING, p INT, l INT",
            rows,
            [
                Expr(
                    "substring",
                    "substring(s, p, l)",
                    lambda row, ansi: _substr_model(*row),
                    "string",
                    "substring(s, p, l)",
                )
            ],
            ibis={"s": "string", "p": "int32", "l": "int32"},
        )
    ]


def _substring_range() -> list[Target]:
    big = [
        2**31 - 1,
        2**31,
        2**31 + 1,
        2**32 - 1,
        2**32,
        2**32 + 1,
        2**32 + 3,
        -(2**31),
        -(2**31) - 1,
        -(2**32) - 1,
        1,
        2,
        -2,
    ]

    def rows(r: random.Random) -> tuple:
        return (
            _rand_str(r),
            pick(r, big, lambda r: r.randint(-(2**34), 2**34), 0.7),
            pick(r, big, lambda r: r.randint(-5, 10), 0.4),
        )

    def model(row: tuple, ansi: bool) -> Any:
        s, p, ln = row
        if s is None:
            return None
        if ansi and (not fits(p, 32) or not fits(ln, 32)):
            return Raise("CAST_OVERFLOW")
        return _substr_model(s, wrap(p, 32), wrap(ln, 32))

    return [
        Target(
            "spark-substring-range",
            "s STRING, p BIGINT, l BIGINT",
            rows,
            [Expr("substring", "substring(s, p, l)", model, "string", "substring(s, p, l)")],
            ibis={"s": "string", "p": "int64", "l": "int64"},
        )
    ]


_PATTERNS = [
    r"(\d+)",
    r"(\w)(\w)",
    r"a(b)?c",
    r"(.)\1",
    r"^(\s*)x",
    r"(é+)",
    r"([a-c]+)-(\d)",
    r"(?<=a)(b)",
]


def _regex() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        alphabet = "ab c1-é٣\nx"
        s = (
            None
            if r.random() < 0.05
            else "".join(r.choice(alphabet) for _ in range(r.randint(0, 8)))
        )
        return (s, r.randrange(len(_PATTERNS)))

    def pat(i: int) -> re.Pattern:
        return re.compile(_PATTERNS[i], re.ASCII)

    def rlike(row: tuple, ansi: bool) -> Any:
        s, i = row
        return None if s is None else pat(i).search(s) is not None

    def extract(row: tuple, ansi: bool) -> Any:
        s, i = row
        if s is None:
            return None
        m = pat(i).search(s)
        return "" if m is None or m.group(1) is None else m.group(1)

    def replace(row: tuple, ansi: bool) -> Any:
        s, i = row
        if s is None:
            return None
        return pat(i).sub(lambda m: "<" + (m.group(1) or "") + ">", s)

    case = (
        "CASE i "
        + " ".join(
            f"WHEN {k} THEN '{p.replace(chr(92), chr(92) * 2)}'" for k, p in enumerate(_PATTERNS)
        )
        + " END"
    )
    return [
        Target(
            "spark-regex",
            "s STRING, i INT",
            rows,
            [
                Expr("rlike", f"s RLIKE ({case})", rlike, "boolean"),
                Expr("regexp_extract", f"regexp_extract(s, {case}, 1)", extract, "string"),
                Expr("regexp_replace", f"regexp_replace(s, {case}, '<$1>')", replace, "string"),
            ],
            note="Patterns with a group 1, chosen per row; Python's re with ASCII classes as the model of java.util.regex.",
        )
    ]


def _list_index() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        a = (
            None
            if r.random() < 0.08
            else [None if r.random() < 0.15 else r.randint(-9, 9) for _ in range(r.randint(0, 4))]
        )
        return (a, r.randint(-6, 6))

    def element_at(row: tuple, ansi: bool) -> Any:
        a, i = row
        if a is None:
            return None
        if i == 0:
            return Raise("INVALID_INDEX_OF_ZERO")
        k = i - 1 if i > 0 else len(a) + i
        if 0 <= k < len(a):
            return a[k]
        return Raise("INVALID_ARRAY_INDEX_IN_ELEMENT_AT") if ansi else None

    def bracket(row: tuple, ansi: bool) -> Any:
        a, i = row
        if a is None:
            return None
        if 0 <= i < len(a):
            return a[i]
        return Raise("INVALID_ARRAY_INDEX") if ansi else None

    def get(row: tuple, ansi: bool) -> Any:
        a, i = row
        return None if a is None or not 0 <= i < len(a) else a[i]

    def try_at(row: tuple, ansi: bool) -> Any:
        a, i = row
        if a is None:
            return None
        if i == 0:
            return Raise("INVALID_INDEX_OF_ZERO")
        v = element_at(row, False)
        return v

    def size(row: tuple, ansi: bool) -> Any:
        a, _ = row
        return (None if ansi else -1) if a is None else len(a)

    return [
        Target(
            "spark-list-index",
            "a ARRAY<INT>, i INT",
            rows,
            [
                Expr("element_at", "element_at(a, i)", element_at, "int", "list_extract(a, i)"),
                Expr("a[i]", "a[i]", bracket, "int"),
                Expr("get", "get(a, i)", get, "int"),
                Expr("try_element_at", "try_element_at(a, i)", try_at, "int"),
                Expr("size", "size(a)", size, "int"),
                Expr(
                    "array_size",
                    "array_size(a)",
                    lambda row, ansi: None if row[0] is None else len(row[0]),
                    "int",
                ),
            ],
            ibis={"a": "array<int32>", "i": "int32"},
        )
    ]


def _list_cmp(a: list, b: list) -> int:
    for x, y in zip(a, b, strict=False):
        if x == y:
            continue
        if x is None:
            return -1
        if y is None:
            return 1
        return -1 if x < y else 1
    return (len(a) > len(b)) - (len(a) < len(b))


def _list_order() -> list[Target]:
    def arr(r: random.Random) -> list | None:
        if r.random() < 0.05:
            return None
        return [None if r.random() < 0.25 else r.randint(0, 2) for _ in range(r.randint(0, 3))]

    def cmp(op: Callable[[int], bool]) -> Callable[[tuple, bool], Any]:
        def m(row: tuple, ansi: bool) -> Any:
            a, b = row
            return None if a is None or b is None else op(_list_cmp(a, b))

        return m

    def sort_array(asc: bool) -> Callable[[tuple, bool], Any]:
        def m(row: tuple, ansi: bool) -> Any:
            a = row[0]
            if a is None:
                return None
            nulls = [x for x in a if x is None]
            vals = sorted(x for x in a if x is not None)
            return nulls + vals if asc else vals[::-1] + nulls

        return m

    def array_sort(row: tuple, ansi: bool) -> Any:
        a = row[0]
        return (
            None
            if a is None
            else sorted(x for x in a if x is not None) + [x for x in a if x is None]
        )

    return [
        Target(
            "spark-list-order",
            "a ARRAY<INT>, b ARRAY<INT>",
            lambda r: (arr(r), arr(r)),
            [
                Expr("<", "a < b", cmp(lambda c: c < 0), "boolean"),
                Expr("=", "a = b", cmp(lambda c: c == 0), "boolean"),
                Expr(">", "a > b", cmp(lambda c: c > 0), "boolean"),
                Expr(
                    "greatest",
                    "greatest(a, b)",
                    lambda row, ansi: (
                        None
                        if row[0] is None and row[1] is None
                        else (
                            row[1]
                            if row[0] is None
                            else row[0]
                            if row[1] is None
                            else (row[0] if _list_cmp(row[0], row[1]) >= 0 else row[1])
                        )
                    ),
                    "array<int>",
                ),
                Expr("sort_array asc", "sort_array(a)", sort_array(True), "array<int>"),
                Expr("sort_array desc", "sort_array(a, false)", sort_array(False), "array<int>"),
                Expr("array_sort", "array_sort(a)", array_sort, "array<int>"),
            ],
        )
    ]


_INT_TEXT = re.compile(r"^[+-]?\d+$")
_JAVA_DOUBLE = re.compile(
    r"^[+-]?(NaN|Infinity|((\d+\.?\d*|\.\d+)([eE][+-]?\d+)?)|(0[xX](\p{XDigit}+\.?|\p{XDigit}*\.\p{XDigit}+)[pP][+-]?\d+))[fFdD]?$".replace(
        r"\p{XDigit}", "[0-9a-fA-F]"
    )
)
_WS = "".join(chr(c) for c in range(33))


def _cast_string() -> list[Target]:
    tokens = ["1", "-1", "+7", " 12 ", "\t3\n", "1.5", "-2.5", "1e3", "0x10", "12abc", "", "1_000", "nan", "NaN", "-nan", "inf", "-Infinity", "+Inf",
              "1.5d", "1.5f", "0x1p3", ".5", "5.", "1e400", "1e-400", "2147483647", "2147483648", "-2147483649", "true", "Yes", "n", "T", "0", "maybe", "  yes  "]  # fmt: skip

    def rows(r: random.Random) -> tuple:
        s = r.choice(tokens)
        if r.random() < 0.3:
            s = r.choice([" ", "\t", ""]) + s + r.choice([" ", "\n", ""])
        return (s,)

    def to_int(row: tuple, ansi: bool) -> Any:
        s = row[0].strip(_WS)
        if _INT_TEXT.match(s):
            v = int(s)
        elif not ansi and re.match(r"^[+-]?\d+\.\d*$", s):
            v = int(s.split(".")[0] or "0")
        else:
            return Raise("CAST_INVALID_INPUT") if ansi else None
        if not fits(v, 32):
            return Raise("CAST_INVALID_INPUT") if ansi else None
        return v

    def to_double(row: tuple, ansi: bool) -> Any:
        s = row[0].strip(_WS)
        low = s.lower()
        special = {
            "nan": math.nan,
            "inf": math.inf,
            "+inf": math.inf,
            "infinity": math.inf,
            "+infinity": math.inf,
            "-inf": -math.inf,
            "-infinity": -math.inf,
        }
        if low in special:
            return special[low]
        if not _JAVA_DOUBLE.match(s):
            return Raise("CAST_INVALID_INPUT") if ansi else None
        t = s.rstrip("fFdD")
        if "x" in t.lower():
            return float.fromhex(t)
        return float(t)

    def to_bool(row: tuple, ansi: bool) -> Any:
        s = row[0].strip(_WS).lower()
        if s in ("t", "true", "y", "yes", "1"):
            return True
        if s in ("f", "false", "n", "no", "0"):
            return False
        return Raise("CAST_INVALID_INPUT") if ansi else None

    return [
        Target(
            "spark-cast-string",
            "s STRING",
            rows,
            [
                Expr("to int", "CAST(s AS INT)", to_int, "int"),
                Expr("to double", "CAST(s AS DOUBLE)", to_double, "double", None, same_double),
                Expr("to boolean", "CAST(s AS BOOLEAN)", to_bool, "boolean"),
                Expr(
                    "try_cast int",
                    "try_cast(s AS INT)",
                    lambda row, ansi: (lambda v: None if isinstance(v, Raise) else v)(
                        to_int(row, True)
                    ),
                    "int",
                ),
            ],
            note="Strings from the fact's examples, with whitespace around them.",
        ),
        Target(
            "spark-cast-string",
            "x DOUBLE",
            lambda r: (dbl(r, 0.3),),
            [
                Expr(
                    "double to string",
                    "CAST(x AS STRING)",
                    lambda row, ansi: None if row[0] is None else _java_double(row[0]),
                    "string",
                )
            ],
            note="Formatting modelled as JDK 19's Double.toString: the shortest decimal, scientific outside [1e-3, 1e7).",
        ),
    ]


def _try_variants() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        def v() -> int | None:
            return None if r.random() < 0.05 else pick(r, INT_EDGES["BIGINT"], rand_int(64), 0.6)

        s = r.choice(["1", "x", "2147483648", "-3", "1.5", ""])
        return (v(), v(), s)

    def t(f: Callable[[int, int], int | None]) -> Callable[[tuple, bool], Any]:
        def m(row: tuple, ansi: bool) -> Any:
            a, b, _ = row
            if a is None or b is None:
                return None
            v = f(a, b)
            return v if v is not None and fits(v, 64) else None

        return m

    def tcast(row: tuple, ansi: bool) -> Any:
        s = row[2]
        return int(s) if _INT_TEXT.match(s) and fits(int(s), 32) else None

    return [
        Target(
            "spark-try-variants",
            "a BIGINT, b BIGINT, s STRING",
            rows,
            [
                Expr("try_add", "try_add(a, b)", t(lambda a, b: a + b), "bigint"),
                Expr("try_subtract", "try_subtract(a, b)", t(lambda a, b: a - b), "bigint"),
                Expr("try_multiply", "try_multiply(a, b)", t(lambda a, b: a * b), "bigint"),
                Expr(
                    "try_mod",
                    "try_mod(a, b)",
                    t(lambda a, b: None if b == 0 else tmod(a, b)),
                    "bigint",
                ),
                Expr(
                    "try_divide",
                    "try_divide(a, b)",
                    lambda row, ansi: (
                        None
                        if row[0] is None or row[1] is None or row[1] == 0
                        else float(row[0]) / float(row[1])
                    ),
                    "double",
                    None,
                    same_double,
                ),
                Expr("try_cast", "try_cast(s AS INT)", tcast, "int"),
            ],
        )
    ]


def _raise_set() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        return (
            r.randint(-5, 5),
            r.choice(["1", "1.5", "x", " 2 ", "", "1e2"]),
            [1, 2, 3],
            r.randint(-4, 4),
        )

    def plus_str(row: tuple, ansi: bool) -> Any:
        n, s, _, _ = row
        t = s.strip(_WS)
        if ansi:
            return n + int(t) if _INT_TEXT.match(t) else Raise("CAST_INVALID_INPUT")
        try:
            return float(n) + float(t)
        except ValueError:
            return None

    def at(row: tuple, ansi: bool) -> Any:
        _, _, a, i = row
        if i == 0:
            return Raise("INVALID_INDEX_OF_ZERO")
        k = i - 1 if i > 0 else len(a) + i
        return (
            a[k]
            if 0 <= k < len(a)
            else (Raise("INVALID_ARRAY_INDEX_IN_ELEMENT_AT") if ansi else None)
        )

    return [
        Target(
            "spark-raise-set",
            "n INT, s STRING, a ARRAY<INT>, i INT",
            rows,
            [
                Expr(
                    "int + string",
                    "n + s",
                    plus_str,
                    lambda ansi: "bigint" if ansi else "double",
                    None,
                    same_double,
                ),
                Expr("element_at", "element_at(a, i)", at, "int"),
            ],
            note="Also the raising rows of spark-substring-range, spark-list-index, spark-decimal-negate, spark-round and spark-date-range.",
        )
    ]


def _date_range() -> list[Target]:
    days = [
        2932896,
        2932897,
        -719162,
        -719163,
        0,
        19723,
    ]  # 9999-12-31, +1, 0001-01-01, -1, 1970, 2024
    adds = [1, -1, 2**31 - 1, -(2**31), 2**31 - 19723, 365, 0]

    def rows(r: random.Random) -> tuple:
        return (
            pick(r, days, lambda r: r.randint(-800000, 3000000)),
            pick(r, adds, lambda r: r.randint(-(2**31), 2**31 - 1)),
        )

    micros_max = 2**63 - 1

    def ts_rows(r: random.Random) -> tuple:
        us = pick(
            r,
            [micros_max - 86400 * 10**6 + 1, micros_max - 86400 * 10**6, 253402300799 * 10**6, 0],
            lambda r: r.randint(-(2**62), 2**62),
        )
        return (us, r.choice([1, -1, 10, 100000, 106751991]))

    def ts_add(row: tuple, ansi: bool) -> Any:
        us, n = row
        v = us + n * 86400 * 10**6
        return v if fits(v, 64) else Raise("java.lang.ArithmeticException")

    return [
        Target(
            "spark-date-range",
            "k INT, n INT",
            rows,
            [
                Expr(
                    "date_add",
                    "unix_date(date_add(date_from_unix_date(k), n))",
                    lambda row, ansi: wrap(row[0] + row[1], 32),
                    "int",
                ),
                Expr(
                    "date + 1",
                    "unix_date(date_from_unix_date(k) + 1)",
                    lambda row, ansi: wrap(row[0] + 1, 32),
                    "int",
                ),
            ],
            note="Day counts compared through unix_date: past 9999-12-31 and before 0001-01-01 computed, past 2^31 days wrapped.",
        ),
        Target(
            "spark-date-range",
            "us BIGINT, n INT",
            ts_rows,
            [
                Expr(
                    "ts + interval days",
                    "unix_micros(CAST(timestamp_micros(us) AS TIMESTAMP_NTZ) + make_dt_interval(n, 0, 0, 0))",
                    ts_add,
                    "bigint",
                )
            ],
            note="TIMESTAMP_NTZ + days past the microsecond range: a bare ArithmeticException (SP-3).",
        ),
    ]


# --- Targets: aggregates ----------------------------------------------------
#
# Aggregate targets hold rows (g, x, …). Spark scans a local table in
# `spark.sql.leafNodeDefaultParallelism` slices of consecutive rows
# (`ParallelCollectionRDD`), aggregates each slice in input order, and
# merges the partial results. `_slices` cuts a group's rows the same way, so
# the models can follow the fact's algorithm.


def _slices(n_rows: int, k: int) -> list[range]:
    return [range(i * n_rows // k, (i + 1) * n_rows // k) for i in range(k)]


@dataclass
class Group:
    """One group's values, cut into the scan's slices (in input order)."""

    parts: list[list[Any]]

    @property
    def values(self) -> list[Any]:
        return [v for p in self.parts for v in p]


def _sum_double(parts: list[list[float | None]]) -> list[Any]:
    """Every result `sum` can give: each slice summed in order from NULL
    (`coalesce(sum, 0.0) + x`), the partials merged in any order."""
    partials = []
    for p in parts:
        acc = None
        for x in p:
            if x is not None:
                acc = (0.0 if acc is None else acc) + x
        if acc is not None:
            partials.append(acc)
    if not partials:
        return [None]
    import itertools

    out = []
    for perm in itertools.permutations(partials):
        acc = None
        for x in perm:
            acc = (0.0 if acc is None else acc) + x
        out.append(acc)
    return out


def _any_of(got: Any, allowed: Any) -> bool:
    return any(same_double(got, a) if isinstance(got, float) else got == a for a in allowed)


def _welford(parts: list[list[float]]) -> tuple[float, float, float] | None:
    """(n, avg, m2) after Welford per slice and Chan's merge."""
    states = []
    for p in parts:
        n, avg, m2 = 0.0, 0.0, 0.0
        for x in p:
            if x is None:
                continue
            delta = x - avg
            n += 1
            delta_n = delta / n
            avg += delta_n
            m2 += delta * (delta - delta_n)
        states.append((n, avg, m2))
    n, avg, m2 = 0.0, 0.0, 0.0
    for n2, avg2, m22 in states:
        if n2 == 0:
            continue
        nn = n + n2
        delta = avg2 - avg if n > 0 else 0.0
        delta_n = delta / nn
        avg = avg + delta_n * n2
        m2 = m2 + m22 + delta * delta_n * n * n2
        n = nn
    return (n, avg, m2) if n else None


def _aggregates() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        g = r.randint(0, 60)
        x = dbl(r, 0.15)
        if x is not None and r.random() < 0.5:
            x = r.choice([1e16, -1e16, 1.0, 0.1, 1e9 + r.randint(0, 20)])
        return (g, x)

    def sum_m(parts: list, ansi: bool) -> Any:
        return _sum_double(parts)

    def avg_m(parts: list, ansi: bool) -> Any:
        n = sum(1 for p in parts for x in p if x is not None)
        return [None if s is None else s / n for s in _sum_double(parts)]

    def var(sample: bool, sqrt: bool, legacy: Callable[[], bool]) -> Callable[[list, bool], Any]:
        def m(parts: list, ansi: bool) -> Any:
            st = _welford(parts)
            if st is None:
                return [None]
            n, _, m2 = st
            if sample and n == 1:
                return [math.nan if legacy() else None]
            v = m2 / (n - 1 if sample else n)
            return [nd(np.sqrt, v) if sqrt else v]

        return m

    def mm(f: Callable) -> Callable[[list, bool], Any]:
        def m(parts: list, ansi: bool) -> Any:
            xs = [x for p in parts for x in p if x is not None]
            if not xs:
                return [None]
            if any(math.isnan(x) for x in xs):
                return (
                    [math.nan]
                    if f is max
                    else [min(x for x in xs if not math.isnan(x))]
                    if any(not math.isnan(x) for x in xs)
                    else [math.nan]
                )
            return [f(xs)]

        return m

    state = {"legacy": False}
    sample_rel = close(1e-12)

    def tol(got: Any, allowed: Any) -> bool:
        return any(sample_rel(got, a) or same_double(got, a) for a in allowed)

    return [
        Target(
            "spark-sum-double",
            "g INT, x DOUBLE",
            rows,
            [
                Expr("sum", "sum(x)", sum_m, "double", None, _any_of),
                Expr("avg", "avg(x)", avg_m, "double", None, _any_of),
                Expr("max", "max(x)", mm(max), "double", None, _any_of),
                Expr("min", "min(x)", mm(min), "double", None, _any_of),
            ],
            group=True,
            conf=[
                {"spark.sql.leafNodeDefaultParallelism": "1"},
                {"spark.sql.leafNodeDefaultParallelism": "2"},
                {"spark.sql.leafNodeDefaultParallelism": "3"},
            ],
            note="Bit for bit against the fact's order: each scan slice summed in input order, the partials merged in any order; avg the same sum over the count.",
        ),
        Target(
            "spark-var-stddev",
            "g INT, x DOUBLE",
            rows,
            [
                Expr(
                    "var_samp",
                    "var_samp(x)",
                    var(True, False, lambda: state["legacy"]),
                    "double",
                    None,
                    tol,
                ),
                Expr(
                    "var_pop",
                    "var_pop(x)",
                    var(False, False, lambda: state["legacy"]),
                    "double",
                    None,
                    tol,
                ),
                Expr(
                    "stddev_samp",
                    "stddev_samp(x)",
                    var(True, True, lambda: state["legacy"]),
                    "double",
                    None,
                    tol,
                ),
            ],
            group=True,
            conf=[
                {
                    "spark.sql.legacy.statisticalAggregate": "false",
                    "spark.sql.leafNodeDefaultParallelism": "2",
                },
                {
                    "spark.sql.legacy.statisticalAggregate": "true",
                    "spark.sql.leafNodeDefaultParallelism": "3",
                },
            ],  # fmt: skip
            note="Welford per slice and Chan's merge, within 1e-12 relative.",
        ),
    ]


def _int_sums() -> list[Target]:
    edges = [I64 - 1, -I64, 1, -1, -2, 2, I64 // 2, 0]

    def rows(r: random.Random) -> tuple:
        return (r.randint(0, 40), None if r.random() < 0.05 else pick(r, edges, rand_int(64), 0.6))

    def sum_m(parts: list, ansi: bool) -> Any:
        import itertools

        xs = [x for p in parts for x in p if x is not None]
        if not xs:
            return [None]
        if not ansi:
            return [wrap(sum(xs), 64)]
        partials = []
        for p in parts:
            acc = None
            for x in p:
                if x is None:
                    continue
                acc = (0 if acc is None else acc) + x
                if not fits(acc, 64):
                    return [Raise("ARITHMETIC_OVERFLOW")]
            if acc is not None:
                partials.append(acc)
        outs = []
        for perm in itertools.permutations(partials):
            acc, bad = 0, False
            for x in perm:
                acc += x
                bad = bad or not fits(acc, 64)
            outs.append(Raise("ARITHMETIC_OVERFLOW") if bad else acc)
        return outs

    def avg_m(parts: list, ansi: bool) -> Any:
        xs = [x for p in parts for x in p if x is not None]
        if not xs:
            return [None]
        out = []
        for s in _sum_double([[float(x) if x is not None else None for x in p] for p in parts]):
            out.append(s / len(xs))
        return out

    def narrow(r: random.Random) -> tuple:
        return (r.randint(0, 40), pick(r, [I32 - 1, -I32, 0, 1], rand_int(32), 0.7))

    return [
        Target(
            "spark-sum-int",
            "g INT, x BIGINT",
            rows,
            [
                Expr("sum", "sum(x)", sum_m, "bigint", None, _any_of),
                Expr(
                    "try_sum",
                    "try_sum(x)",
                    lambda parts, ansi: (
                        [None if isinstance(v, Raise) else v for v in sum_m(parts, True)]
                        + (
                            [wrap(sum(x for p in parts for x in p if x is not None), 64)]
                            if False
                            else []
                        )
                    ),
                    "bigint",
                    None,
                    _any_of,
                ),
            ],
            group=True,
            conf=[
                {"spark.sql.leafNodeDefaultParallelism": "1"},
                {"spark.sql.leafNodeDefaultParallelism": "2"},
                {"spark.sql.leafNodeDefaultParallelism": "3"},
            ],
            note="ANSI: raises when a partial sum of a slice, in input order, or of the merge passes 64 bits; off: the wrapped total.",
        ),
        Target(
            "spark-sum-int",
            "g INT, x INT",
            narrow,
            [
                Expr(
                    "sum int",
                    "sum(x)",
                    lambda parts, ansi: (
                        [None]
                        if all(x is None for p in parts for x in p)
                        else [sum(x for p in parts for x in p if x is not None)]
                    ),
                    "bigint",
                    None,
                    _any_of,
                )
            ],
            group=True,
        ),
        Target(
            "spark-avg-int",
            "g INT, x BIGINT",
            rows,
            [Expr("avg", "avg(x)", avg_m, "double", None, _any_of)],
            group=True,
            conf=[{"spark.sql.leafNodeDefaultParallelism": "2"}],
            note="The sum in DOUBLE in the order of spark-sum-double, over the count.",
        ),
    ]


def _co(parts: list) -> tuple | None:
    """Spark's covariance state per slice and merge: (n, xAvg, yAvg, ck, xMk, yMk)."""
    states = []
    for p in parts:
        n = xa = ya = ck = xm = ym = 0.0
        for x, y in p:
            if x is None or y is None:
                continue
            n += 1
            dx = x - xa
            dxn = dx / n
            dy = y - ya
            dyn = dy / n
            xa += dxn
            ya += dyn
            ck += dx * (y - ya)
            xm += dx * (x - xa)
            ym += dy * (y - ya)
        states.append((n, xa, ya, ck, xm, ym))
    n = xa = ya = ck = xm = ym = 0.0
    for n2, xa2, ya2, ck2, xm2, ym2 in states:
        if n2 == 0:
            continue
        nn = n + n2
        dx = xa2 - xa
        dxn = dx / nn if n else 0.0
        dy = ya2 - ya
        dyn = dy / nn if n else 0.0
        if n == 0:
            n, xa, ya, ck, xm, ym = n2, xa2, ya2, ck2, xm2, ym2
            continue
        xa += dxn * n2
        ya += dyn * n2
        ck += ck2 + dx * dyn * n * n2
        xm += xm2 + dx * dxn * n * n2
        ym += ym2 + dy * dyn * n * n2
        n = nn
    return (n, xa, ya, ck, xm, ym) if n else None


def _covar_corr() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        def v() -> float | None:
            if r.random() < 0.05:
                return None
            return r.choice([1.0, 2.0, 3.0, 1e9 + r.randint(0, 9), r.uniform(-10, 10), 0.0])

        return (r.randint(0, 50), v(), v())

    def cov(sample: bool) -> Callable[[list, bool], Any]:
        def m(parts: list, ansi: bool) -> Any:
            st = _co(parts)
            if st is None:
                return [None]
            n, _, _, ck, _, _ = st
            if sample and n == 1:
                return [None]
            return [ck / (n - 1 if sample else n)]

        return m

    def corr(parts: list, ansi: bool) -> Any:
        st = _co(parts)
        if st is None:
            return [None]
        n, _, _, ck, xm, ym = st
        if n == 1 or xm == 0 or ym == 0:
            return [None]
        d = nd(np.sqrt, xm * ym)
        if d == 0:
            return [Raise("DIVIDE_BY_ZERO") if ansi else None]
        return [ck / d]

    t = close(1e-9)

    def tol(got: Any, allowed: Any) -> bool:
        return any(t(got, a) for a in allowed)

    return [
        Target(
            "spark-covar",
            "g INT, x DOUBLE, y DOUBLE",
            rows,
            [
                Expr("covar_samp", "covar_samp(x, y)", cov(True), "double", None, tol),
                Expr("covar_pop", "covar_pop(x, y)", cov(False), "double", None, tol),
            ],
            group=True,
            conf=[{"spark.sql.leafNodeDefaultParallelism": "2"}],
        ),
        Target(
            "spark-corr",
            "g INT, x DOUBLE, y DOUBLE",
            rows,
            [Expr("corr", "corr(x, y)", corr, "double", None, tol)],
            group=True,
            conf=[{"spark.sql.leafNodeDefaultParallelism": "2"}],
            note="Within 1e-9 relative; not clamped to [-1, 1].",
        ),
    ]


def _quantile() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        return (
            r.randint(0, 50),
            None if r.random() < 0.08 else r.choice([r.randint(-5, 5), r.randint(-1000, 1000)]),
        )

    def cont(p: float) -> Callable[[list, bool], Any]:
        def m(parts: list, ansi: bool) -> Any:
            xs = sorted(float(x) for q in parts for x in q if x is not None)
            if not xs:
                return [None]
            pos = (len(xs) - 1) * p
            lo, hi = math.floor(pos), math.ceil(pos)
            if lo == hi:
                return [xs[lo]]
            return [(hi - pos) * xs[lo] + (pos - lo) * xs[hi]]

        return m

    def disc(p: float) -> Callable[[list, bool], Any]:
        def m(parts: list, ansi: bool) -> Any:
            xs = sorted(float(x) for q in parts for x in q if x is not None)
            if not xs:
                return [None]
            n = len(xs)
            for i, x in enumerate(xs):
                if (i + 1) / n >= p:
                    return [x]
            return [xs[-1]]

        return m

    c = close(1e-15)
    exprs = []
    for p in (0.0, 0.25, 0.5, 0.9, 1.0):
        exprs.append(
            Expr(
                f"percentile_cont {p}",
                f"percentile_cont({p}) WITHIN GROUP (ORDER BY x)",
                cont(p),
                "double",
                None,
                lambda g, a: any(c(g, x) for x in a),
            )
        )
        exprs.append(
            Expr(
                f"percentile_disc {p}",
                f"percentile_disc({p}) WITHIN GROUP (ORDER BY x)",
                disc(p),
                "double",
                None,
                _any_of,
            )
        )
    exprs.append(
        Expr("median", "median(x)", cont(0.5), "double", None, lambda g, a: any(c(g, x) for x in a))
    )
    return [Target("spark-quantile", "g INT, x INT", rows, exprs, group=True)]


def _nonfinite() -> list[Target]:
    def rows(r: random.Random) -> tuple:
        return (
            r.randint(0, 40),
            r.choice([math.inf, -math.inf, math.nan, 1e308, 1.0, -1.0, 0.0, None]),
        )

    t = _aggregates()
    sum_e, avg_e, max_e, min_e = t[0].exprs
    var_e = t[1].exprs[0]
    return [
        Target(
            "spark-nonfinite-aggregates",
            "g INT, x DOUBLE",
            rows,
            [
                sum_e,
                avg_e,
                max_e,
                min_e,
                Expr(
                    "var_samp",
                    "var_samp(x)",
                    var_e.model,
                    "double",
                    None,
                    lambda g, a: any(same_double(g, x) or close(1e-12)(g, x) for x in a),
                ),
            ],
            group=True,
            conf=[{"spark.sql.leafNodeDefaultParallelism": "2"}],
            note="Values only ±inf, NaN, 1e308, ±1, 0 and NULL.",
        )
    ]


def targets() -> dict[str, list[Target]]:
    """The targets by name; each name covers one fact (some facts several)."""
    found = {
        "int_divide": _int_divide(),
        "int_shift": _int_shift(),
        "int_pow": _int_pow(),
        "decimal_negate": _decimal_negate(),
        "size_limits": _size_limits(),
        "double_arith": _double_arith(),
        "double_divide_mod": _double_divide_mod(),
        "elem_rounding": _elem_rounding(),
        "math_domain": _math_domain(),
        "nan_sign": _nan_sign(),
        "zero_sign": _zero_sign(),
        "zero_order": _zero_order(),
        "round": _round(),
        "fp32": _fp32(),
        "substring": _substring(),
        "substring_range": _substring_range(),
        "regex": _regex(),
        "list_index": _list_index(),
        "list_order": _list_order(),
        "cast_string": _cast_string(),
        "try_variants": _try_variants(),
        "raise_set": _raise_set(),
        "date_range": _date_range(),
        "aggregates": _aggregates(),
        "int_sums": _int_sums(),
        "covar_corr": _covar_corr(),
        "quantile": _quantile(),
        "nonfinite": _nonfinite(),
    }
    return found


# --- Running ----------------------------------------------------------------


def _error(e: BaseException) -> Raise:
    for name in ("getCondition", "getErrorClass"):
        fn = getattr(e, name, None)
        if fn is not None:
            try:
                cond = fn()
            except Exception:  # noqa: BLE001
                cond = None
            if cond:
                return Raise(str(cond))
    m = re.search(r"(java\.[\w.$]+(Exception|Error))", str(e))
    return Raise(m.group(1) if m else type(e).__name__)


def _norm(v: Any) -> Any:
    if hasattr(v, "asDict"):
        return v.asDict()
    if isinstance(v, list):
        return [_norm(x) for x in v]
    return v


class Spark:
    """One local session; tables are temp views dropped after each batch."""

    def __init__(self) -> None:
        import os

        from pyspark.sql import SparkSession

        os.environ["TZ"] = "UTC"
        time.tzset()
        b = SparkSession.builder.appName("sverify-spark-fuzz")
        for k, v in CONF.items():
            b = b.config(k, v)
        self.spark = b.getOrCreate()
        self.spark.sparkContext.setLogLevel("OFF")
        # pyspark logs every query error it raises; they are results here.
        logging.getLogger("pyspark").setLevel(logging.CRITICAL)
        logging.getLogger("SQLQueryContextLogger").setLevel(logging.CRITICAL)

    def settings(self, ansi: bool, path: str, extra: dict[str, str]) -> None:
        c = self.spark.conf
        c.set("spark.sql.ansi.enabled", str(ansi).lower())
        if path == "codegen":
            c.set("spark.sql.optimizer.excludedRules", CODEGEN_EXCLUDED)
        else:
            c.unset("spark.sql.optimizer.excludedRules")
        for k in ("spark.sql.leafNodeDefaultParallelism", "spark.sql.legacy.statisticalAggregate"):
            c.unset(k)
        for k, v in extra.items():
            c.set(k, v)

    def view(self, columns: str, rows: list[tuple]) -> None:
        df = self.spark.createDataFrame(rows, schema=f"id INT, {columns}", verifySchema=False)
        df.createOrReplaceTempView("t")

    def drop(self) -> None:
        self.spark.catalog.dropTempView("t")

    def query(self, sql: str) -> tuple[list[tuple], str] | Raise:
        try:
            df = self.spark.sql(sql)
            rows = [tuple(_norm(x) for x in r) for r in df.collect()]
            return rows, df.schema.fields[-1].dataType.simpleString()
        except Exception as e:  # noqa: BLE001 - an error is a result
            return _error(e)

    def stop(self) -> None:
        self.spark.stop()


@dataclass
class Stats:
    rows: int = 0
    runs: int = 0
    raised: Counter = field(default_factory=Counter)
    agree: int = 0
    lean_compared: int = 0
    lean_differs: int = 0
    findings: list[dict] = field(default_factory=list)


def _matches(e: Expr, got: Any, want: Any) -> bool:
    if isinstance(want, Raise) or isinstance(got, Raise):
        return isinstance(want, Raise) and isinstance(got, Raise) and got.cls == want.cls
    if e.same is not None:
        return e.same(got, want)
    if isinstance(want, float) and isinstance(got, float):
        return same_double(got, want)
    return got == want


def _expected_type(e: Expr, ansi: bool) -> str | None:
    return e.type(ansi) if callable(e.type) else e.type


def _lean(t: Target, e: Expr, rows: list[tuple]) -> list[Any] | None:
    """`Rel.eval`'s values of the DuckDB form on the rows (by position)."""
    if e.duckdb is None or t.ibis is None or t.group:
        return None
    import ibis

    from sverify.sql_lift import lift
    from sverify.testing import inline_tables, lean_values

    try:
        names = list(t.ibis)
        lifted = lift(
            f"SELECT {e.duckdb} AS r FROM t", {"t": ibis.schema(t.ibis)}, semantics="reference"
        )
        plan = inline_tables(copy.deepcopy(lifted.plan), {"t": [r[: len(names)] for r in rows]})
        return [v[0] for v in lean_values(json.dumps(plan))]
    except Exception as ex:  # noqa: BLE001 - outside the lift or the model
        print(f"  lean: {e.name}: {str(ex)[:160]}", file=sys.stderr)
        return None


def _lean_same(a: Any, b: Any) -> bool:
    if isinstance(a, float) and isinstance(b, (float, int)):
        if math.isnan(a):
            return isinstance(b, float) and math.isnan(b)
        return abs(a - b) <= 1e-6 * max(1.0, abs(a))
    if isinstance(a, Decimal) and b is not None:
        return Decimal(str(b)) == a
    return a == b


def _finding(stats: Stats, t: Target, e: Expr, setting: str, row: Any, got: Any, want: Any) -> None:
    if len([f for f in stats.findings if f["expr"] == e.name]) >= 5:
        return
    stats.findings.append({
        "expr": e.name, "sql": e.spark, "setting": setting, "input": _show(row),
        "spark": _show(got), "fact": _show(want),
    })  # fmt: skip
    print(
        f"  FINDING {e.name} [{setting}] {_show(row)}: spark {_show(got)}, fact {_show(want)}",
        flush=True,
    )


def _show(v: Any) -> Any:
    if isinstance(v, Raise):
        return str(v)
    if isinstance(v, float):
        if math.isnan(v):
            return "-NaN" if math.copysign(1, v) < 0 else "NaN"
        return repr(v)
    if isinstance(v, (Decimal, dt.date)):
        return str(v)
    if isinstance(v, (list, tuple)):
        return [_show(x) for x in v]
    if isinstance(v, Group):
        return [_show(p) for p in v.parts]
    return v


def run_scalar(
    sp: Spark, t: Target, rows: list[tuple], stats: Stats, sample: int, rng: random.Random
) -> None:
    table = [(i, *r) for i, r in enumerate(rows)]
    sp.view(t.columns, table)
    try:
        for e in t.exprs:
            lean = _lean(t, e, rows)
            for extra in t.conf:
                for ansi in (True, False):
                    want = [e.model(r, ansi) for r in rows]
                    for path in PATHS:
                        setting = f"ansi={str(ansi).lower()} {path}" + "".join(
                            f" {k.split('.')[-1]}={v}" for k, v in extra.items()
                        )
                        sp.settings(ansi, path, extra)
                        stats.runs += 1
                        ok = [i for i, w in enumerate(want) if not isinstance(w, Raise)]
                        bad = [i for i, w in enumerate(want) if isinstance(w, Raise)]
                        _batch(sp, t, e, ok, rows, want, stats, setting, ansi, lean)
                        for i in rng.sample(bad, min(sample, len(bad))):
                            got = sp.query(f"SELECT id, {e.spark} FROM t WHERE id = {i}")
                            g = got if isinstance(got, Raise) else got[0][0][1]
                            stats.rows += 1
                            if isinstance(g, Raise):
                                stats.raised[g.cls] += 1
                            if _matches(e, g, want[i]):
                                stats.agree += 1
                            else:
                                _finding(stats, t, e, setting, rows[i], g, want[i])
    finally:
        sp.drop()


def _batch(sp: Spark, t: Target, e: Expr, ids: list[int], rows: list[tuple], want: list[Any],
           stats: Stats, setting: str, ansi: bool, lean: list[Any] | None) -> None:  # fmt: skip
    if not ids:
        return
    where = f"id IN ({', '.join(map(str, ids))})"
    got = sp.query(f"SELECT id, {e.spark} FROM t WHERE {where}")
    if isinstance(got, Raise):
        if len(ids) == 1:
            stats.rows += 1
            stats.raised[got.cls] += 1
            _finding(stats, t, e, setting, rows[ids[0]], got, want[ids[0]])
            return
        mid = len(ids) // 2
        _batch(sp, t, e, ids[:mid], rows, want, stats, setting, ansi, lean)
        _batch(sp, t, e, ids[mid:], rows, want, stats, setting, ansi, lean)
        return
    values, typ = got
    expected = _expected_type(e, ansi)
    if expected is not None and typ != expected:
        _finding(stats, t, e, setting, "result type", typ, expected)
    for i, v in values:
        stats.rows += 1
        if _matches(e, v, want[i]):
            stats.agree += 1
        else:
            _finding(stats, t, e, setting, rows[i], v, want[i])
        if lean is not None and setting.startswith("ansi=true folded"):
            stats.lean_compared += 1
            if not _lean_same(v, lean[i]):
                stats.lean_differs += 1


def run_grouped(sp: Spark, t: Target, rows: list[tuple], stats: Stats) -> None:
    table = [(i, *r) for i, r in enumerate(rows)]
    sp.view(t.columns, table)
    try:
        for extra in t.conf:
            k = int(extra.get("spark.sql.leafNodeDefaultParallelism", "2"))
            groups: dict[Any, Group] = {}
            for s in _slices(len(rows), k):
                for g in sorted({rows[i][0] for i in s}):
                    groups.setdefault(g, Group([[] for _ in range(k)]))
                for i in s:
                    vals = rows[i][1:]
                    groups[rows[i][0]].parts[_slices(len(rows), k).index(s)].append(
                        vals[0] if len(vals) == 1 else vals
                    )
            for e in t.exprs:
                for ansi in (True, False):
                    legacy = extra.get("spark.sql.legacy.statisticalAggregate") == "true"
                    _set_legacy(t, legacy)
                    want = {g: e.model(grp.parts, ansi) for g, grp in groups.items()}
                    for path in PATHS:
                        setting = f"ansi={str(ansi).lower()} {path}" + "".join(
                            f" {k2.split('.')[-1]}={v}" for k2, v in extra.items()
                        )
                        sp.settings(ansi, path, extra)
                        stats.runs += 1
                        _group_batch(sp, t, e, sorted(groups), groups, want, stats, setting, ansi)
    finally:
        sp.drop()


def _set_legacy(t: Target, legacy: bool) -> None:
    for e in t.exprs:
        cells = getattr(e.model, "__closure__", None) or ()
        for c in cells:
            try:
                v = c.cell_contents
            except ValueError:
                continue
            if callable(v) and getattr(v, "__name__", "") == "<lambda>":
                st = next(
                    (
                        cc.cell_contents
                        for cc in (v.__closure__ or ())
                        if isinstance(cc.cell_contents, dict) and "legacy" in cc.cell_contents
                    ),
                    None,
                )
                if st is not None:
                    st["legacy"] = legacy


def _group_batch(sp: Spark, t: Target, e: Expr, keys: list, groups: dict, want: dict,
                 stats: Stats, setting: str, ansi: bool) -> None:  # fmt: skip
    if not keys:
        return
    expected_raise = [g for g in keys if all(isinstance(w, Raise) for w in want[g])]
    keys = [g for g in keys if g not in expected_raise] if len(keys) > 1 else keys
    for g in expected_raise[:3] if len(keys) != 1 or keys[0] not in expected_raise else []:
        _group_batch(sp, t, e, [g], groups, want, stats, setting, ansi)
    if not keys:
        return
    where = f"g IN ({', '.join(map(str, keys))})"
    got = sp.query(f"SELECT g, {e.spark} FROM t WHERE {where} GROUP BY g")
    if isinstance(got, Raise):
        if len(keys) == 1:
            stats.rows += 1
            stats.raised[got.cls] += 1
            if any(_matches(e, got, w) for w in want[keys[0]]):
                stats.agree += 1
            else:
                _finding(stats, t, e, setting, groups[keys[0]], got, want[keys[0]])
            return
        mid = len(keys) // 2
        _group_batch(sp, t, e, keys[:mid], groups, want, stats, setting, ansi)
        _group_batch(sp, t, e, keys[mid:], groups, want, stats, setting, ansi)
        return
    values, typ = got
    expected = _expected_type(e, ansi)
    if expected is not None and typ != expected:
        _finding(stats, t, e, setting, "result type", typ, expected)
    for g, v in values:
        stats.rows += 1
        w = want[g]
        ok = e.same(v, w) if e.same is not None else v in w
        if ok:
            stats.agree += 1
        else:
            _finding(stats, t, e, setting, groups[g], v, w)


def run(
    names: Sequence[str],
    n_rows: int,
    seed: int,
    sample: int,
    save: Callable[[dict], None] | None = None,
) -> dict[str, Any]:
    import pyspark

    all_targets = targets()
    sp = Spark()
    out: dict[str, Any] = {}
    try:
        for name in names:
            for k, t in enumerate(all_targets[name]):
                rng = random.Random(f"{seed}:{name}:{k}")
                rows = [t.rows(rng) for _ in range(n_rows)]
                stats = Stats()
                t0 = time.monotonic()
                print(f"{name}[{k}] {t.fact}: {len(rows)} rows", flush=True)
                if t.group:
                    rows.sort(key=lambda r: r[0])
                try:
                    if t.group:
                        run_grouped(sp, t, rows, stats)
                    else:
                        run_scalar(sp, t, rows, stats, sample, rng)
                except Exception as e:  # noqa: BLE001 - a harness error stops this target only
                    stats.findings.append({"harness": f"{type(e).__name__}: {e}"[:300]})
                    print(f"  HARNESS {type(e).__name__}: {e}", flush=True)
                out[f"{name}[{k}]"] = {
                    "fact": t.fact,
                    "seed": seed,
                    "columns": t.columns,
                    "constructs": [e.spark for e in t.exprs],
                    "settings": sorted(
                        {tuple(sorted(c.items())) for c in t.conf}
                        and [" ".join(f"{k2}={v}" for k2, v in c.items()) for c in t.conf]
                    ),
                    "input_rows": len(rows),
                    "runs": stats.runs,
                    "results": stats.rows,
                    "agree": stats.agree,
                    "raised": dict(stats.raised),
                    "lean_compared": stats.lean_compared,
                    "lean_differs": stats.lean_differs,
                    "findings": stats.findings,
                    "seconds": round(time.monotonic() - t0, 1),
                    "note": t.note,
                }
                if save is not None:
                    save(out)
                print(f"  {stats.agree}/{stats.rows} agree, {len(stats.findings)} finding(s), "
                      f"Rel.eval differs on {stats.lean_differs}/{stats.lean_compared}", flush=True)  # fmt: skip
        out["_meta"] = {
            "spark": pyspark.__version__,
            "java": sp.spark._jvm.System.getProperty("java.version"),
            "os": f"{sp.spark._jvm.System.getProperty('os.name')} {sp.spark._jvm.System.getProperty('os.arch')}",
            "conf": CONF,
            "paths": "ansi true and false; folded and codegen (ConvertToLocalRelation, ConstantFolding excluded)",
            "date": dt.date.today().isoformat(),
        }
    finally:
        sp.stop()
    return out


def dry(names: Sequence[str], n_rows: int, seed: int) -> list[str]:
    """Run every model on the targets' rows, without Spark: the models'
    errors (a harness bug) as messages."""
    errors = []
    for name in names:
        for k, t in enumerate(targets()[name]):
            rows = [t.rows(random.Random(f"{seed}:{name}:{k}")) for _ in range(1)]
            rng = random.Random(f"{seed}:{name}:{k}")
            rows = [t.rows(rng) for _ in range(n_rows)]
            for e in t.exprs:
                for ansi in (True, False):
                    try:
                        if t.group:
                            for extra in t.conf:
                                n = int(extra.get("spark.sql.leafNodeDefaultParallelism", "2"))
                                for s in _slices(len(rows), n):
                                    vals = [
                                        r[1] if len(r) == 2 else r[1:] for r in (rows[i] for i in s)
                                    ]
                                    e.model([vals], ansi)
                        else:
                            for r in rows:
                                e.model(r, ansi)
                    except Exception as ex:  # noqa: BLE001
                        errors.append(
                            f"{name}[{k}] {e.name} ansi={ansi}: {type(ex).__name__}: {ex}"
                        )
    print("\n".join(errors) or "every model ran")
    return errors


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("targets", nargs="*", help="target names (default: all)")
    parser.add_argument(
        "--rows", type=int, default=300, help="random input rows per target (default 300)"
    )
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument(
        "--sample",
        type=int,
        default=15,
        help="raising rows run one by one, per construct and setting",
    )
    parser.add_argument("--out", type=Path, default=OUT)
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--dry", action="store_true", help="run the models only, without Spark")
    args = parser.parse_args(argv)
    names = args.targets or list(targets())
    if args.list:
        for n, ts in targets().items():
            print(n, ", ".join(sorted({t.fact for t in ts})))
        return
    if args.dry:
        sys.exit(1 if dry(names, args.rows, args.seed) else 0)
    old = json.loads(args.out.read_text()) if args.out.is_file() else {}

    def save(found: dict) -> None:
        args.out.write_text(
            json.dumps({**old, **found}, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
        )

    result = run(names, args.rows, args.seed, args.sample, save)
    save(result)
    n = sum(len(v["findings"]) for k, v in result.items() if k != "_meta")
    print(f"{n} finding(s) -> {args.out}")


if __name__ == "__main__":
    main()

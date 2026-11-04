"""Probe Polars's expressions for the Substrait options they implement.

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API. The Polars counterpart of `sverify_dev.probe` (#242), for the Polars
characterization (`characterization/polars/`).

Two kinds of probe:

- A `Probe` is a Polars expression at one signature, with the Substrait call
  that may describe it. Polars evaluates it on edge cases (zero, ±1, the
  bounds of the integer width, ±inf, NaN, NULL), one row at a time; Lean
  evaluates the Substrait call on the same rows once per candidate value of
  its option (`substrait-check --outcomes`), as `sverify_dev.probe` does for
  DuckDB. The candidates whose outcomes all match are Polars's options.
- An `Observation` is a short Polars program whose result the reference has
  no single call for: a sort, a grouping, a cast's failure, a date. Its
  `observed` value is recorded as it is.

`python -m sverify_dev.probe_polars --write` writes
`characterization/polars/probes.json`; the facts in
`characterization/polars/facts/` cite its constructs, and
`tests/test_probe_polars.py` checks it is current. Those run on the
in-memory engine: eager `DataFrame` methods always do.

`--diff` compares the streaming engine, which sverify targets (#605), with
the in-memory one, without Lean: each probe one row at a time and on a
column of `TILE` rows (several morsels, no length-1 column: PL-3), and each
observation; `--diff --write` writes `probes-streaming.json`, the evidence of
the facts' streaming checks. `--engine streaming` runs the probes against
Lean on the streaming engine: a probe's frame is collected lazily with
`engine="streaming"`, and an observation's `df(...)` is a `StreamingFrame`,
whose `select`, `with_columns`, `filter`, `sort`, `unique`, `join` and
`group_by(...).agg` go through `LazyFrame.collect(engine="streaming")`.
"""

from __future__ import annotations

import argparse
import datetime as dt
import itertools
import json
import math
import struct
from collections.abc import Callable, Sequence
from dataclasses import dataclass
from decimal import Decimal
from pathlib import Path
from typing import Any, Literal

import polars as pl

from sverify_dev.probe import STRINGS, Outcome, Probe, encode_double, lean_outcomes

Json = dict[str, Any]

OUT = Path(__file__).resolve().parents[3] / "characterization" / "polars" / "probes.json"
#: Where `--engine streaming --write` writes.
OUT_STREAMING = OUT.with_name("probes-streaming.json")
#: The engine probes and observations run on: `in-memory` or `streaming`.
ENGINE = "in-memory"


def _ints(bits: int) -> list[int | None]:
    hi = 2 ** (bits - 1)
    return [0, 1, -1, 2, -2, 3, 7, -7, hi - 1, -hi, None]


# No -0.0, as for DuckDB: the model has one zero.
DOUBLES: list[float | None] = [
    0.0, 0.5, 1.0, -1.0, 2.5, -2.5, 7.0, 1e308, math.inf, -math.inf, math.nan, None
]  # fmt: skip

#: Ibis's type names (the Lean side's) and Polars's types, with their edge cases.
TYPES: dict[str, tuple[Any, list[Any]]] = {
    "int8": (pl.Int8, _ints(8)),
    "int16": (pl.Int16, _ints(16)),
    "int32": (pl.Int32, _ints(32)),
    "int64": (pl.Int64, _ints(64)),
    "float64": (pl.Float64, DOUBLES),
    # DuckDB's probe strings, and two that are not ASCII.
    "string": (pl.String, [*STRINGS[:-1], "héllo", "ß", None]),
}

WIDTHS = ("int8", "int16", "int32", "int64")
OVERFLOW = ("ERROR", "SILENT", "SATURATE")


def _int_probes(w: str) -> list[Probe]:
    two = (w, w)
    return [
        Probe("{0} + {1}", "add", two, w, "overflow", OVERFLOW),
        Probe("{0} - {1}", "subtract", two, w, "overflow", OVERFLOW),
        Probe("{0} * {1}", "multiply", two, w, "overflow", OVERFLOW),
        Probe("-{0}", "negate", (w,), w, "overflow", OVERFLOW),
        Probe("{0}.abs()", "abs", (w,), w, "overflow", OVERFLOW),
        Probe("{0} // {1}", "divide", two, w, "on_division_by_zero", ("ERROR", "NULL")),
        Probe("{0} % {1}", "modulus", two, w, "on_division_by_zero", ("ERROR", "NULL")),
        # `.mod` is `%`, under a name of its own so the construct is unique.
        Probe("{0}.mod({1})", "modulus", two, w, "division_type", ("TRUNCATE", "FLOOR"),
              fixed={"on_division_by_zero": "NULL"}),
    ]  # fmt: skip


F = ("float64",)
FF = ("float64", "float64")
S = ("string",)
SS = ("string", "string")

PROBES: list[Probe] = [
    *itertools.chain.from_iterable(_int_probes(w) for w in WIDTHS),
    Probe("{0} + {1}", "add", FF, "float64"),
    Probe("{0} - {1}", "subtract", FF, "float64"),
    Probe("{0} * {1}", "multiply", FF, "float64"),
    Probe("{0} / {1}", "divide", FF, "float64",
          "on_division_by_zero", ("ERROR", "IEEE", "NULL", "LIMIT")),
    Probe("{0} % {1}", "modulus", FF, "float64"),
    Probe("{0} ** {1}", "power", FF, "float64"),
    Probe("{0}.floor()", "floor", F, "float64"),
    Probe("{0}.ceil()", "ceil", F, "float64"),
    Probe("{0}.round()", "round", F, "float64",
          "rounding", ("TIE_TO_EVEN", "TIE_AWAY_FROM_ZERO")),
    Probe("{0}.round(mode='half_away_from_zero')", "round", F, "float64",
          "rounding", ("TIE_TO_EVEN", "TIE_AWAY_FROM_ZERO")),
    # To `d` digits (#335). Negative digits are refused by the Python API.
    *(
        Probe(f"{{0}}.round({d})", "round", F, "float64", constants=((d, "int64"),))
        for d in (1, 2, 16, 308, 309, 400)
    ),
    *(
        Probe(f"{{0}}.{m}()", f, F, "float64")
        for m, f in [("sqrt", "sqrt"), ("exp", "exp"), ("log", "ln"), ("log10", "log10"),
                     ("sin", "sin"), ("cos", "cos"), ("tan", "tan"), ("arcsin", "asin"),
                     ("arccos", "acos"), ("arctan", "atan")]
    ),
    Probe("{0}.log(2)", "log2", F, "float64"),
    Probe("pl.arctan2({0}, {1})", "atan2", FF, "float64"),
    # Comparisons of doubles: NaN's equality and order (`nan_equality`, `nan_order`).
    Probe("{0} == {1}", "equal", FF, "boolean"),
    Probe("{0} < {1}", "lt", FF, "boolean"),
    Probe("{0}.is_null()", "is_null", F, "boolean"),
    Probe("pl.max_horizontal({0}, {1})", "greatest", FF, "float64"),
    Probe("pl.min_horizontal({0}, {1})", "least", FF, "float64"),
    # Strings. A constant argument is written into the construct and passed
    # to Lean as `constants`.
    Probe("{0}.str.to_uppercase()", "upper", S, "string"),
    Probe("{0}.str.to_lowercase()", "lower", S, "string"),
    Probe("{0}.str.len_chars()", "character_length", S, "int64"),
    Probe("{0}.str.reverse()", "reverse", S, "string"),
    Probe("{0}.str.strip_chars(' ')", "btrim", S, "string", constants=((" ", "string"),)),
    Probe("pl.concat_str({0}, {1})", "str_concat", SS, "string"),
    *(
        Probe(f"{{0}}.str.{m}({c!r})", f, S, "boolean", constants=((c, "string"),))
        for m, f in [("starts_with", "starts_with"), ("ends_with", "ends_with")]
        for c in ("a", "")
    ),
    *(
        Probe(f"{{0}}.str.find({c!r}, literal=True)", "strpos", S, "int64",
              constants=((c, "string"),))
        for c in ("a", "b", "")
    ),
    Probe("{0}.str.replace_all('a', 'xy', literal=True)", "replace", S, "string",
          constants=(("a", "string"), ("xy", "string"))),
    *(
        Probe(f"{{0}}.str.slice({o}, {n})", "substring", S, "string",
              constants=((o + 1 if o >= 0 else o, "int64"), (n, "int64")))
        for o, n in [(0, 2), (1, 2), (-2, 5), (-10, 3), (5, 1)]
    ),
    # Regular expressions with a constant pattern (#50), as for DuckDB.
    *(
        Probe(f"{{0}}.str.extract({pat!r}, {g})", "regexp_extract", S, "string",
              constants=((pat, "string"), (g, "int64")))
        for pat, g in [("^(a+)(b)?", 2), ("(a|ab)(c|bcd)?", 0), ("(a*)*", 1),
                       ("x(?:a)(y)", 1), (".$", 0), ("(b)", 1)]
    ),
    *(
        Probe(f"{{0}}.str.replace_all({pat!r}, {r!r})", "regexp_replace", S, "string",
              constants=((pat, "string"), (r, "string"), ("g", "string")))
        for pat, r in [("a+", "-"), ("b*", "-"), ("$", "!")]
    ),
]  # fmt: skip


@dataclass(frozen=True)
class Observation:
    """A Polars program and what it gives."""

    construct: str
    """Its name, which facts cite."""
    area: str
    code: str
    """A Python expression over `pl`, `math`, `dt`, `Decimal`, `inf`, `nan` and
    the helpers `df`, `bits`, `attempt`."""


def _o(construct: str, area: str, code: str) -> Observation:
    return Observation(construct, area, code)


def df(**cols: Any) -> pl.DataFrame:
    """A frame of the given columns (`df(x=[...])`), each a list or a
    `(list, dtype)` pair; a `StreamingFrame` when `ENGINE` is `streaming`."""
    frame = pl.DataFrame(
        {k: v[0] if isinstance(v, tuple) else v for k, v in cols.items()},
        schema_overrides={k: v[1] for k, v in cols.items() if isinstance(v, tuple)},
    )
    return StreamingFrame.of(frame) if ENGINE == "streaming" else frame


class StreamingFrame(pl.DataFrame):
    """A `DataFrame` whose relational methods run on the streaming engine:
    each is the `LazyFrame` method collected with `engine="streaming"`, and
    gives a `StreamingFrame` again, so chains stay on streaming. Other
    methods (`item`, `to_series`, Series operations) run eagerly on the
    collected result."""

    @staticmethod
    def of(frame: pl.DataFrame) -> StreamingFrame:
        out = StreamingFrame.__new__(StreamingFrame)
        out._df = frame._df
        return out

    def _run(self, name: str, *args: Any, **kwargs: Any) -> StreamingFrame:
        lazy = getattr(self.lazy(), name)(*args, **kwargs)
        return StreamingFrame.of(lazy.collect(engine="streaming"))

    def select(self, *args: Any, **kwargs: Any) -> StreamingFrame:  # type: ignore[override]
        return self._run("select", *args, **kwargs)

    def with_columns(self, *args: Any, **kwargs: Any) -> StreamingFrame:  # type: ignore[override]
        return self._run("with_columns", *args, **kwargs)

    def filter(self, *args: Any, **kwargs: Any) -> StreamingFrame:  # type: ignore[override]
        return self._run("filter", *args, **kwargs)

    def sort(self, *args: Any, **kwargs: Any) -> StreamingFrame:  # type: ignore[override]
        return self._run("sort", *args, **kwargs)

    def unique(self, *args: Any, **kwargs: Any) -> StreamingFrame:  # type: ignore[override]
        return self._run("unique", *args, **kwargs)

    def join(self, other: pl.DataFrame, *args: Any, **kwargs: Any) -> StreamingFrame:  # type: ignore[override]
        lazy = self.lazy().join(other.lazy(), *args, **kwargs)
        return StreamingFrame.of(lazy.collect(engine="streaming"))

    def group_by(self, *by: Any, **kwargs: Any) -> _StreamingGroupBy:  # type: ignore[override]
        return _StreamingGroupBy(self, by, kwargs)


@dataclass(frozen=True)
class _StreamingGroupBy:
    frame: StreamingFrame
    by: tuple[Any, ...]
    kwargs: dict[str, Any]

    def agg(self, *aggs: Any, **named: Any) -> StreamingFrame:
        lazy = self.frame.lazy().group_by(*self.by, **self.kwargs).agg(*aggs, **named)
        return StreamingFrame.of(lazy.collect(engine="streaming"))

    def __getattr__(self, name: str) -> Callable[..., StreamingFrame]:
        """`len`, `first`, `sum`, …: the lazy group-by's method, collected
        on streaming."""
        method = getattr(self.frame.lazy().group_by(*self.by, **self.kwargs), name)
        return lambda *a, **k: StreamingFrame.of(method(*a, **k).collect(engine="streaming"))


OBSERVATIONS: list[Observation] = [
    # Integers.
    _o("int-sum-types", "integers",
       "{t: (str(df(x=([1], t)).select(pl.col('x').sum()).dtypes[0]),"
       " df(x=([2**(b-1)-1, 1], t)).select(pl.col('x').sum()).item())"
       " for t, b in [(pl.Int8, 8), (pl.Int16, 16), (pl.Int32, 32), (pl.Int64, 64)]}"),
    _o("int-sum-grouped", "integers",
       "[df(g=[1, 1], x=([2**(b-1)-1, 1], t)).group_by('g').agg(pl.col('x').sum()).item(0, 'x')"
       " for t, b in [(pl.Int8, 8), (pl.Int32, 32), (pl.Int64, 64)]]"),
    _o("int-sum-empty", "integers",
       "[df(x=([None, None], pl.Int64)).select(pl.col('x').sum()).item(),"
       " df(x=([], pl.Int64)).select(pl.col('x').sum()).item(),"
       " df(g=[1], x=([None], pl.Int64)).group_by('g').agg(pl.col('x').sum()).item(0, 'x'),"
       " df(x=([], pl.Int64)).select(pl.col('x').product()).item()]"),
    _o("int-mean", "integers",
       "(df(x=[2**62, 2**62, 1]).select(pl.col('x').mean()).item(),"
       " str(df(x=[1, 2]).select(pl.col('x').mean()).dtypes[0]),"
       " df(x=([None], pl.Int64)).select(pl.col('x').mean()).item(),"
       " df(x=[1, 2]).select(pl.col('x').median()).item())"),
    _o("int-true-divide", "integers",
       "df(a=[7, -7, 0, 1], b=[2, 0, 0, 3]).select(pl.col('a') / pl.col('b'))"
       ".to_series().to_list()"),
    _o("int-pow", "integers",
       "(df(x=[2, 3, -2]).select(pl.col('x') ** 63).to_series().to_list(),"
       " str(df(x=([2], pl.Int32)).select(pl.col('x') ** pl.col('x')).dtypes[0]))"),
    _o("int-pow-negative", "integers", "df(x=[2]).select(pl.col('x') ** -1).item()"),
    _o("int-shift", "integers",
       "[m for m in dir(pl.Expr) if 'shift' in m and 'bit' in m]"),
    # Doubles.
    _o("zero-sign-arith", "doubles",
       "df(z=[-0.0, 0.0]).select((1.0 / pl.col('z')).alias('inv'), (-pl.col('z')).alias('neg'),"
       " (pl.col('z') * -1.0).alias('mul'), pl.col('z').sqrt().alias('sqrt')).rows()"),
    # `inf - inf`'s NaN has the platform's sign (x86's is negative), so only
    # a NaN of known sign goes in.
    _o("nan-sign-negate", "doubles",
       "[bits(v) for v in df(z=[nan]).select(-pl.col('z'), pl.col('z').abs().alias('abs'),"
       " (-pl.col('z')).sqrt().alias('sqrt')).row(0)]"),
    _o("double-floordiv", "doubles",
       "df(a=[7.0, -7.0, 1.0, inf, 5.0], b=[2.0, 2.0, 0.0, 2.0, inf])"
       ".select(pl.col('a') // pl.col('b')).to_series().to_list()"),
    _o("double-modulus-sign", "doubles",
       "df(a=[5.5, -5.5, 5.5, -5.5, 5.0, -5.0], b=[2.0, 2.0, -2.0, -2.0, inf, inf])"
       ".select(pl.col('a') % pl.col('b')).to_series().to_list()"),
    _o("round-digits-negative", "doubles", "df(x=[123.0]).select(pl.col('x').round(-1)).item()"),
    _o("round-digits-ties", "doubles",
       "{d: df(x=[0.125, 0.375, 2.675, 1.005, 0.285]).select(pl.col('x').round(d))"
       ".to_series().to_list() for d in (1, 2)}"),
    _o("round-default-mode", "doubles",
       "df(x=[0.5, 1.5, 2.5, -0.5, -2.5]).select(pl.col('x').round()).to_series().to_list()"),
    _o("float-sum-nonfinite", "doubles",
       "df(x=[inf, -inf, 1.0]).select(pl.col('x').sum().alias('sum'),"
       " pl.col('x').mean().alias('mean'), pl.col('x').std().alias('std')).rows()"),
    _o("float-std-inf", "aggregates",
       "df(x=[inf, 1.0]).select(pl.col('x').std().alias('std'),"
       " pl.col('x').var().alias('var')).rows()"),
    _o("float-sum-empty", "aggregates",
       "[df(x=([], pl.Float64)).select(pl.col('x').sum()).item(),"
       " df(x=([None], pl.Float64)).select(pl.col('x').sum()).item(),"
       " df(x=([], pl.Float64)).select(pl.col('x').mean()).item()]"),
    _o("var-one-value", "aggregates",
       "df(x=[1.0]).select(pl.col('x').var().alias('samp'), pl.col('x').var(ddof=0).alias('pop'),"
       " pl.col('x').std().alias('std')).rows()"),
    _o("corr-degenerate", "aggregates",
       "df(x=[1.0, 1.0], y=[1.0, 2.0]).select(pl.corr('x', 'y').alias('const'),"
       " pl.corr(pl.col('x').head(1), pl.col('y').head(1)).alias('one'),"
       " pl.corr(pl.col('x').head(0), pl.col('y').head(0)).alias('none')).rows()"),
    _o("quantile-methods", "aggregates",
       "df(x=[1.0, 2.0, 3.0, 4.0]).select(*(pl.col('x').quantile(0.4, m).alias(m) for m in"
       " ['nearest', 'lower', 'higher', 'midpoint', 'linear', 'equiprobable'])).rows()"),
    _o("quantile-default", "aggregates",
       "df(x=[1.0, 2.0, 3.0, 4.0]).select(pl.col('x').quantile(0.4)).item()"),
    # Decimals.
    _o("decimal-result-types", "decimals",
       "[str(t) for t in df(x=['1.25']).select("
       "(pl.col('x').cast(pl.Decimal(10, 2)) * pl.col('x').cast(pl.Decimal(5, 1))).alias('mul'),"
       " (pl.col('x').cast(pl.Decimal(10, 2)) + pl.col('x').cast(pl.Decimal(5, 1))).alias('add'),"
       " (pl.col('x').cast(pl.Decimal(10, 2)) / pl.col('x').cast(pl.Decimal(5, 1))).alias('div'),"
       " pl.col('x').cast(pl.Decimal(5, 2)).sum().alias('sum')).dtypes]"),
    _o("decimal-rounding", "decimals",
       "{'mul': df(x=['0.05', '0.15', '-0.05']).select(pl.col('x').cast(pl.Decimal(10, 2))"
       " * pl.lit('0.5').cast(pl.Decimal(10, 1))).to_series().to_list(),"
       " 'div': df(x=['1.00', '3.00', '-1.00']).select(pl.col('x').cast(pl.Decimal(10, 2))"
       " / pl.lit('8').cast(pl.Decimal(10, 0))).to_series().to_list(),"
       " 'rescale': df(x=['1.050', '1.150', '-1.050', '1.051']).select(pl.col('x')"
       ".cast(pl.Decimal(10, 3)).cast(pl.Decimal(10, 1))).to_series().to_list(),"
       " 'from_double': df(x=[0.625, 0.375, -0.625, 0.135]).select(pl.col('x')"
       ".cast(pl.Decimal(10, 2))).to_series().to_list()}"),
    _o("decimal-overflow", "decimals",
       "df(x=['9999.99']).select(pl.col('x').cast(pl.Decimal(6, 2))"
       " * pl.lit(1000).cast(pl.Decimal(6, 0))).item()"),
    _o("decimal-precision-38", "decimals",
       "df(x=['9' * 36 + '.99']).select(pl.col('x').cast(pl.Decimal(38, 2))"
       " * pl.lit(10).cast(pl.Decimal(2, 0))).item()"),
    _o("decimal-divide-by-zero", "decimals",
       "df(x=['1.00']).select(pl.col('x').cast(pl.Decimal(6, 2))"
       " / pl.lit(0).cast(pl.Decimal(6, 0))).item()"),
    _o("decimal-mean", "decimals",
       "(df(x=['1.00', '2.01']).select(pl.col('x').cast(pl.Decimal(5, 2)).mean()).item(),"
       " str(df(x=['1.00']).select(pl.col('x').cast(pl.Decimal(5, 2)).mean()).dtypes[0]))"),
    # NaN, -0.0 and NULL: equality, order, grouping.
    _o("nan-compare", "doubles",
       "df(a=[nan, nan, 1.0, inf, 0.0, None], b=[nan, 1.0, nan, nan, -0.0, None]).select("
       "(pl.col('a') == pl.col('b')).alias('eq'), (pl.col('a') < pl.col('b')).alias('lt'),"
       " (pl.col('a') > pl.col('b')).alias('gt'), pl.col('a').eq_missing(pl.col('b')).alias('eqm'))"
       ".rows()"),
    _o("nan-is-in", "doubles",
       "df(a=[nan, 1.0, None]).select(pl.col('a').is_in([nan])).to_series().to_list()"),
    _o("sort-doubles", "relations",
       "{f'{d=} {n=}': df(x=[1.0, nan, None, -inf, inf, 0.0, -1.0])"
       ".sort('x', descending=d, nulls_last=n)['x'].to_list()"
       " for d in (False, True) for n in (False, True)}"),
    _o("sort-zero-sign", "relations",
       "df(x=[0.0, -0.0, 0.0, -0.0], i=[0, 1, 2, 3]).sort('x', maintain_order=True).rows()"),
    _o("sort-null-default", "relations",
       "[df(x=[2, None, 1]).sort('x', descending=d)['x'].to_list() for d in (False, True)]"),
    _o("sort-strings-bools", "relations",
       "(df(s=['b', 'B', 'a', 'é', 'Z', '', None]).sort('s')['s'].to_list(),"
       " df(s=[True, None, False]).sort('s')['s'].to_list())"),
    _o("sort-stable", "relations",
       "[df(k=[i % 7 for i in range(200_000)], i=range(200_000)).lazy()"
       ".sort('k', maintain_order=m).collect(engine=e)"
       ".select((pl.col('i').diff().over('k') < 0).any()).item()"
       " for m in (False, True) for e in ('in-memory', 'streaming')]"),
    _o("min-max-nan", "aggregates",
       "df(x=[1.0, nan, None, -inf, inf]).select(pl.col('x').min().alias('min'),"
       " pl.col('x').max().alias('max'), pl.col('x').nan_min().alias('nan_min'),"
       " pl.col('x').nan_max().alias('nan_max'), pl.col('x').arg_max().alias('arg_max'),"
       " pl.col('x').sort().last().alias('sort_last')).rows()"),
    _o("min-max-only-nan", "aggregates",
       "df(x=[nan, None]).select(pl.col('x').min().alias('min'), pl.col('x').max().alias('max'))"
       ".rows()"),
    _o("median-nan", "aggregates",
       "df(x=[1.0, 2.0, nan]).select(pl.col('x').median().alias('median'),"
       " pl.col('x').quantile(0.5, 'lower').alias('lower')).rows()"),
    _o("group-nan-zero", "relations",
       "df(x=[1.0, nan, None, nan, 0.0, -0.0, None]).group_by('x', maintain_order=True)"
       ".agg(pl.len()).rows()"),
    _o("unique-nan-zero", "relations",
       "(df(x=[nan, 0.0, -0.0, nan, None, None]).unique(maintain_order=True)['x'].to_list(),"
       " df(x=[nan, 0.0, -0.0, nan, None]).select(pl.col('x').n_unique()).item())"),
    _o("join-nan-zero-null", "relations",
       "[df(x=[nan, 0.0, -0.0, None]).join(df(x=[nan, 0.0, None], y=[1, 2, 3]), on='x',"
       " nulls_equal=n).sort('y').rows() for n in (False, True)]"),
    _o("int-float-compare", "doubles",
       "df(i=[2**53 + 1], f=[2.0**53]).select((pl.col('i') == pl.col('f')).alias('eq'),"
       " (pl.col('i') > pl.col('f')).alias('gt')).rows()"),
    # NULLs in logic and aggregates.
    _o("kleene", "relations",
       "df(a=[True, False, None, None], b=[None, None, None, True]).select("
       "(pl.col('a') & pl.col('b')).alias('and'), (pl.col('a') | pl.col('b')).alias('or'),"
       " (~pl.col('a')).alias('not')).rows()"),
    _o("any-all-nulls", "aggregates",
       "df(x=[True, None]).select(pl.col('x').all().alias('all'),"
       " pl.col('x').all(ignore_nulls=False).alias('all_kleene'),"
       " pl.col('x').any(ignore_nulls=False).alias('any_kleene')).rows()"),
    _o("count-nulls", "aggregates",
       "df(x=[1, None, None]).select(pl.col('x').count().alias('count'),"
       " pl.col('x').len().alias('len'), pl.col('x').null_count().alias('nulls')).rows()"),
    _o("aggregates-empty", "aggregates",
       "df(x=([None, None], pl.Int64)).select(pl.col('x').min().alias('min'),"
       " pl.col('x').first().alias('first'), pl.col('x').count().alias('count'),"
       " pl.col('x').mode().alias('mode').implode()).rows()"),
    # Ties and order inside a group.
    _o("first-last", "aggregates",
       "df(g=[1, 1, 1, 2], x=[None, 3, None, 4]).group_by('g', maintain_order=True)"
       ".agg(pl.col('x').first().alias('first'), pl.col('x').last().alias('last'),"
       " pl.col('x').first(ignore_nulls=True).alias('first_nn'),"
       " pl.col('x').last(ignore_nulls=True).alias('last_nn')).rows()"),
    _o("first-input-order", "aggregates",
       "[df(k=[i % 10 for i in range(200_000)], i=range(200_000)).lazy().group_by('k')"
       ".agg(pl.col('i').first().alias('f'), pl.col('i').min().alias('m'),"
       " pl.col('i').last().alias('l'), pl.col('i').max().alias('M'),"
       " pl.col('i').alias('all')).collect(engine=e)"
       ".select(((pl.col('f') == pl.col('m')) & (pl.col('l') == pl.col('M'))"
       " & (pl.col('all').list.eval(pl.element().diff().drop_nulls().min() > 0).list.first()))"
       ".all()).item() for e in ('in-memory', 'streaming')]"),
    _o("arg-min-max-ties", "aggregates",
       "df(x=[1, 3, 3, 1]).select(pl.col('x').arg_max().alias('arg_max'),"
       " pl.col('x').arg_min().alias('arg_min')).rows()"),
    _o("mode-ties", "aggregates",
       "df(x=[3, 1, 2, 2, 1, 3]).select(pl.col('x').mode().sort()).to_series().to_list()"),
    _o("string-agg", "aggregates",
       "df(g=[1, 1, 1], x=['a', None, 'b']).group_by('g')"
       ".agg(pl.col('x').str.join(',')).item(0, 'x')"),
    _o("top-k-ties", "relations",
       "df(x=[1, 1, 1, 0], i=[0, 1, 2, 3]).top_k(2, by='x').sort('i').rows()"),
    # Windows.
    _o("rank-methods", "windows",
       "df(x=[2, 1, 2, None]).select(*(pl.col('x').rank(m).alias(m) for m in"
       " ['average', 'min', 'max', 'dense', 'ordinal'])).rows()"),
    _o("rank-descending-nan", "windows",
       "df(x=[2.0, nan, 1.0, None]).select(pl.col('x').rank('min').alias('asc'),"
       " pl.col('x').rank('min', descending=True).alias('desc')).rows()"),
    _o("window-lag-first", "windows",
       "df(g=[1, 1, 2], x=[3, 1, 2]).select(pl.col('x').first().over('g').alias('first'),"
       " pl.col('x').shift(1).over('g').alias('lag'),"
       " pl.col('x').cum_sum().over('g').alias('cum')).rows()"),
    # Strings.
    _o("slice", "strings",
       "{f'{o},{n}': df(s=['hello', 'héllo', '', None]).select(pl.col('s').str.slice(o, n))"
       ".to_series().to_list() for o, n in [(0, 2), (1, 2), (-2, None), (-2, 5), (-10, 3),"
       " (-10, 7), (10, 2), (2, None)]}"),
    _o("slice-negative-length", "strings",
       "df(s=['hello']).select(pl.col('s').str.slice(0, -1)).item()"),
    _o("find-bytes", "strings",
       "df(s=['héllo', 'hello', 'xyz', '']).select(pl.col('s').str.find('l', literal=True)"
       ".alias('find'), pl.col('s').str.find('', literal=True).alias('empty')).rows()"),
    _o("len-chars-bytes", "strings",
       "df(s=['héllo', 'ß', 'e\u0301', '']).select(pl.col('s').str.len_chars().alias('chars'),"
       " pl.col('s').str.len_bytes().alias('bytes')).rows()"),
    _o("case-unicode", "strings",
       "df(s=['straße', 'ǅungla', 'İ', 'ΣΑΣ']).select(pl.col('s').str.to_uppercase().alias('up'),"
       " pl.col('s').str.to_lowercase().alias('low')).rows()"),
    _o("reverse-graphemes", "strings",
       "[ascii(v) for v in df(s=['e\u0301x', '\U0001f1e9\U0001f1eaa', 'abc'])"
       ".select(pl.col('s').str.reverse()).to_series().to_list()]"),
    _o("strip-whitespace", "strings",
       "[ascii(v) for v in df(s=[' \\t a \\n', '\u00a0b\u2003', 'xxaxx'])"
       ".select(pl.col('s').str.strip_chars()).to_series().to_list()]"),
    _o("concat-nulls", "strings",
       "df(a=['x', None], b=['y', 'z']).select(pl.concat_str('a', 'b').alias('concat'),"
       " pl.concat_str('a', 'b', ignore_nulls=True).alias('ignore'),"
       " (pl.col('a') + pl.col('b')).alias('plus')).rows()"),
    _o("regex-syntax", "strings",
       "{p: attempt(lambda: df(s=['ab', '\u0663', '\u00e9']).select(pl.col('s').str.contains(p))"
       ".to_series().to_list())"
       " for p in ['a(?=b)', r'(a)\\1', r'^\\d$', r'^\\w$', '(?i)AB', '^[[:alpha:]]+$']}"),
    _o("regex-invalid", "strings", "df(s=['a']).select(pl.col('s').str.contains('(')).item()"),
    _o("regex-replace-refs", "strings",
       "df(s=['aab']).select(pl.col('s').str.replace_all('(a+)', '<$1>').alias('dollar'),"
       " pl.col('s').str.replace_all('(a+)', r'<\\1>').alias('backslash'),"
       " pl.col('s').str.replace_all('(a+)', '<${1}x>').alias('braces'),"
       " pl.col('s').str.replace('a', 'x').alias('first')).rows()"),
    _o("regex-extract-nomatch", "strings",
       "df(s=['xay', 'b', None]).select(pl.col('s').str.extract('(a)', 1).alias('g1'),"
       " pl.col('s').str.extract('(a)?b', 1).alias('unset')).rows()"),
    _o("string-functions-missing", "strings",
       "[n for n in ['levenshtein', 'md5', 'sha256', 'repeat', 'ascii', 'like', 'ilike']"
       " if not hasattr(pl.Expr.str, n)]"),
    # Temporal.
    _o("date-month-arith", "temporal",
       "df(x=[dt.date(2024, 1, 31), dt.date(2024, 2, 29), dt.date(2023, 3, 31)]).select("
       "pl.col('x').dt.offset_by('1mo').alias('+1mo'), pl.col('x').dt.offset_by('-1mo')"
       ".alias('-1mo'), pl.col('x').dt.offset_by('1y').alias('+1y')).rows()"),
    _o("date-range", "temporal",
       "df(x=[dt.date(1, 1, 1), dt.date(9999, 12, 31)]).select("
       "(pl.col('x') + pl.duration(days=d)).cast(pl.String).alias(str(d)) for d in [-1, 1])"
       ".rows()"),
    _o("date-physical-range", "temporal",
       "df(x=([2**31 - 1], pl.Int32)).select(pl.col('x').cast(pl.Date).cast(pl.String)).item()"),
    _o("timestamp-range", "temporal",
       "df(x=[dt.datetime(9999, 1, 1)]).select((pl.col('x') + pl.duration(days=10**6))"
       ".cast(pl.String)).item()"),
    _o("timestamp-unit", "temporal",
       "(str(df(x=[dt.datetime(2024, 1, 1)]).dtypes[0]),"
       " attempt(lambda: df(x=[dt.datetime(2262, 4, 12)]).select(pl.col('x')"
       ".cast(pl.Datetime('ns'))).item()))"),
    _o("date-parts", "temporal",
       "df(x=[dt.datetime(2024, 12, 30, 1, 2, 3, 456789), dt.datetime(2021, 1, 3)]).select("
       "pl.col('x').dt.year().alias('year'), pl.col('x').dt.iso_year().alias('iso_year'),"
       " pl.col('x').dt.week().alias('week'), pl.col('x').dt.weekday().alias('weekday'),"
       " pl.col('x').dt.ordinal_day().alias('doy'), pl.col('x').dt.quarter().alias('q'),"
       " pl.col('x').dt.millisecond().alias('ms'), pl.col('x').dt.microsecond().alias('us'),"
       " pl.col('x').dt.epoch('s').alias('epoch')).rows()"),
    _o("before-epoch", "temporal",
       "df(x=[dt.datetime(1969, 12, 31, 23, 59, 59, 500000)]).select("
       "pl.col('x').dt.truncate('1s').alias('trunc'), pl.col('x').dt.epoch('s').alias('epoch'),"
       " pl.col('x').dt.second().alias('second'),"
       " pl.col('x').dt.microsecond().alias('us')).rows()"),
    _o("truncate-units", "temporal",
       "df(x=[dt.datetime(2024, 12, 31, 13, 7, 3), dt.datetime(2021, 1, 3)]).select("
       "*(pl.col('x').dt.truncate(u).alias(u) for u in ['1w', '1mo', '1q', '1y', '15m'])).rows()"),
    _o("date-diff", "temporal",
       "df(a=[dt.date(2024, 3, 1)], b=[dt.date(2024, 1, 31)]).select("
       "(pl.col('a') - pl.col('b')).alias('diff'),"
       " (pl.col('a') - pl.col('b')).dt.total_days().alias('days')).rows()"),
    _o("strftime", "temporal",
       "df(x=[dt.datetime(2024, 1, 5, 3, 4, 5, 600000)]).select("
       "pl.col('x').dt.strftime('%Y-%m-%d %H:%M:%S%.f %j %a %U %V')).item()"),
    _o("time-plus-duration", "temporal",
       "df(x=[dt.time(23, 0)]).select(pl.col('x') + pl.duration(hours=2)).item()"),
    _o("tz-nonexistent", "temporal",
       "df(x=[dt.datetime(2024, 3, 31, 2, 30)]).select("
       "pl.col('x').dt.replace_time_zone('Europe/Berlin')).item()"),
    _o("str-to-date", "temporal",
       "(df(x=['2024-02-30', '2024-2-3', '2024-02-03']).select(pl.col('x')"
       ".str.to_date('%Y-%m-%d', strict=False)).to_series().to_list(),"
       " df(x=['2024-02-30']).select(pl.col('x').str.to_date('%Y-%m-%d')).item())"),
    # Casts.
    _o("cast-double-to-int", "casts",
       "{str(t): df(x=[2.5, -2.5, 2.7, -2.7, 127.9, 128.0, 1e19, inf, nan, None])"
       ".select(pl.col('x').cast(t, strict=False)).to_series().to_list()"
       " for t in [pl.Int8, pl.Int64]}"),
    _o("cast-double-to-int-strict", "casts",
       "df(x=[1e19]).select(pl.col('x').cast(pl.Int64)).item()"),
    _o("cast-double-to-int-wrap", "casts",
       "df(x=[1e19, -1e19, inf, nan, 300.0, -129.0]).select(pl.col('x')"
       ".cast(pl.Int8, wrap_numerical=True)).to_series().to_list()"),
    _o("cast-int-narrow", "casts",
       "(df(x=[300, -129, 127]).select(pl.col('x').cast(pl.Int8, strict=False))"
       ".to_series().to_list(), df(x=[300, -129, 127]).select(pl.col('x')"
       ".cast(pl.Int8, wrap_numerical=True)).to_series().to_list())"),
    _o("cast-int-narrow-strict", "casts",
       "df(x=[300]).select(pl.col('x').cast(pl.Int8)).item()"),
    _o("cast-int-to-double", "casts",
       "df(x=[2**53 + 1, 2**63 - 1]).select(pl.col('x').cast(pl.Float64)).to_series().to_list()"),
    _o("cast-double-to-float", "casts",
       "df(x=[1e300, 1e-50, 0.1]).select(pl.col('x').cast(pl.Float32)).to_series().to_list()"),
    _o("cast-decimal-to-int", "casts",
       "df(x=['2.5', '-2.5', '2.7']).select(pl.col('x').cast(pl.Decimal(10, 1))"
       ".cast(pl.Int64)).to_series().to_list()"),
    _o("cast-int-to-decimal-overflow", "casts",
       "(df(x=[300, 1234]).select(pl.col('x').cast(pl.Decimal(5, 2), strict=False))"
       ".to_series().to_list(), df(x=[1234]).select(pl.col('x').cast(pl.Decimal(5, 2))).item())"),
    _o("cast-string-to-int", "casts",
       "df(x=['1', ' 2', '3.0', '-0', '+5', '9223372036854775808', '1e2', '', '0x10'])"
       ".select(pl.col('x').cast(pl.Int64, strict=False)).to_series().to_list()"),
    _o("cast-string-to-double", "casts",
       "df(x=['1.5', ' 2', 'nan', 'inf', '-Infinity', '1e400', '.5', '5.', '-0', 'abc'])"
       ".select(pl.col('x').cast(pl.Float64, strict=False)).to_series().to_list()"),
    _o("cast-double-to-string", "casts",
       "df(x=[0.1, 1e21, 1e-7, 1e-5, 1.0, -0.0, inf, nan, 1e15, 1e16, 123456789012345680.0])"
       ".select(pl.col('x').cast(pl.String)).to_series().to_list()"),
    _o("cast-bool", "casts",
       "(df(x=[0, 2, -1]).select(pl.col('x').cast(pl.Boolean)).to_series().to_list(),"
       " df(x=[0.0, -0.0, nan]).select(pl.col('x').cast(pl.Boolean)).to_series().to_list(),"
       " df(x=[True, False]).select(pl.col('x').cast(pl.String)).to_series().to_list())"),
    _o("cast-string-to-bool", "casts",
       "df(x=['true']).select(pl.col('x').cast(pl.Boolean)).item()"),
    _o("cast-string-to-date", "casts",
       "df(x=['2024-01-01']).select(pl.col('x').cast(pl.Date)).item()"),
    # Lists and structs.
    _o("list-sort", "nested",
       "[df(l=[[1, None], [1, 3], [1], [], None, [None], [1, 2]]).sort('l', descending=d)['l']"
       ".to_list() for d in (False, True)]"),
    _o("list-compare", "nested",
       "df(a=[[1, None]], b=[[1, 3]]).select(pl.col('a') < pl.col('b')).item()"),
    _o("list-min", "nested", "df(l=[[1], [2]]).select(pl.col('l').min()).item()"),
    _o("list-equality", "nested",
       "df(a=[[1, None], [None], []], b=[[1, None], [None], None]).select("
       "(pl.col('a') == pl.col('b')).alias('eq'), pl.col('a').eq_missing(pl.col('b')).alias('eqm'))"
       ".rows()"),
    _o("list-get", "nested",
       "(df(l=[[1, 2, 3], [], None]).select(pl.col('l').list.get(0, null_on_oob=True).alias('0'),"
       " pl.col('l').list.get(-1, null_on_oob=True).alias('-1'),"
       " pl.col('l').list.get(5, null_on_oob=True).alias('5')).rows(),"
       " attempt(lambda: df(l=[[1, 2, 3]]).select(pl.col('l').list.get(5)).item()))"),
    _o("struct-equality", "nested",
       "df(s=[{'a': 1, 'b': None}, {'a': 1, 'b': None}, {'a': None, 'b': None}, None]).select("
       "(pl.col('s') == pl.col('s').shift(1)).alias('eq')).to_series().to_list()"),
    _o("struct-group-sort", "nested",
       "(df(s=[{'a': 1, 'b': None}, {'a': 1, 'b': None}, None]).group_by('s', maintain_order=True)"
       ".len().rows(), df(s=[{'a': 2, 'b': 1}, {'a': 1, 'b': None}, {'a': 1, 'b': 0},"
       " {'a': None, 'b': 0}]).sort('s')['s'].to_list())"),
    _o("explode", "nested",
       "(df(i=[1, 2, 3, 4], l=[[1, 2], [], None, [None]]).explode('l').rows(),"
       " df(i=[1, 2, 3, 4], l=[[1, 2], [], None, [None]])"
       ".explode('l', empty_as_null=False, keep_nulls=False).rows())"),
    # Set operations, written as Polars writes them.
    _o("set-operations", "relations",
       "{k: v.rows() for k, v in {"
       "'union_all': pl.concat([df(x=[1, 1, 2, None, None]), df(x=[1, None, 3])]),"
       " 'union': pl.concat([df(x=[1, 1, 2, None, None]), df(x=[1, None, 3])])"
       ".unique(maintain_order=True),"
       " 'semi': df(x=[1, 1, 2, None, None]).join(df(x=[1, None, 3]), on='x', how='semi'),"
       " 'intersect': df(x=[1, 1, 2, None, None]).join(df(x=[1, None, 3]), on='x', how='semi',"
       " nulls_equal=True).unique(maintain_order=True),"
       " 'anti': df(x=[1, 1, 2, None, None]).join(df(x=[1, None, 3]), on='x', how='anti'),"
       " 'except': df(x=[1, 1, 2, None, None]).join(df(x=[1, None, 3]), on='x', how='anti',"
       " nulls_equal=True).unique(maintain_order=True)}.items()}"),
    _o("clustered", "relations",
       "df(k=[2, 1, 2, 1], i=[0, 1, 2, 3]).sort('k', maintain_order=True).rows()"),
    # Strings past 32 bits, fp32, frontend typing.
    _o("substring-huge", "strings",
       "df(s=['abc']).select(pl.col('s').str.slice(2**40, 2**40).alias('far'),"
       " pl.col('s').str.slice(-2**40, 2**41).alias('wide')).rows()"),
    _o("fp32-arith", "doubles",
       "(df(a=([1.0, 3e38, 16777216.0], pl.Float32)).select(pl.col('a') + pl.col('a'),"
       " (pl.col('a') + 1).alias('plus1')).rows(), [str(t) for t in df(a=([0.1], pl.Float32))"
       ".select(pl.col('a') + 0.1, (pl.col('a') + 1).alias('i'), pl.col('a').sum().alias('s'),"
       " pl.col('a').mean().alias('m')).dtypes])"),
    _o("implicit-casts", "frontend",
       "([str(t) for t in df(a=([1], pl.Int32), b=[1]).select(pl.col('a') + pl.col('b'),"
       " (pl.col('a') + 1).alias('lit'), (pl.col('a') + 2**40).alias('big'),"
       " (pl.col('a') + 1.5).alias('f'), (pl.col('a').cast(pl.UInt64) + pl.col('b')).alias('u'))"
       ".dtypes], attempt(lambda: df(a=[1]).select(pl.col('a') + pl.lit('x')).item()))"),
    _o("literal-types", "frontend",
       "[str(t) for t in pl.select(pl.lit(1), pl.lit(2**40).alias('b'), pl.lit(2**63).alias('c'),"
       " pl.lit(2**64).alias('d'), pl.lit(1.5).alias('e'), pl.lit('x').alias('f'),"
       " pl.lit(None).alias('g'), pl.lit(True).alias('h'), pl.lit(Decimal('1.25')).alias('i'))"
       ".dtypes]"),
    _o("type-names", "frontend",
       "[str(t) for t in [pl.Int8, pl.UInt64, pl.Int128, pl.Float32, pl.String, pl.Binary,"
       " pl.Boolean, pl.Date, pl.Time, pl.Datetime('us'), pl.Duration('us'), pl.Decimal(10, 2),"
       " pl.List(pl.Int64), pl.Array(pl.Int64, 2), pl.Struct({'a': pl.Int64}), pl.Null,"
       " pl.Categorical]]"),
    # I/O.
    _o("io-functions", "io",
       "([n for n in dir(pl) if n.startswith('scan_')],"
       " [n for n in dir(pl.DataFrame) if n.startswith('write_')],"
       " [n for n in dir(pl.LazyFrame) if n.startswith('sink_')],"
       " hasattr(pl, 'Catalog'),"
       " [p for p in ('storage_options', 'credential_provider')"
       " if p in __import__('inspect').signature(pl.scan_parquet).parameters])"),
]  # fmt: skip


def bits(x: float) -> str:
    """A double's bits, in hex."""
    return hex(struct.unpack("<Q", struct.pack("<d", x))[0])


def attempt(f: Callable[[], Any]) -> Any:
    """`f()`, or the error it raises as text."""
    try:
        return f()
    except Exception as e:
        return f"error {type(e).__name__}: {str(e).splitlines()[0]}"


def _col(i: int) -> str:
    return f"pl.col('a{i}')"


def _expr(p: Probe) -> pl.Expr:
    return eval(p.construct.format(*(_col(i) for i in range(len(p.args)))), {"pl": pl})


def polars_outcome(p: Probe, row: Sequence[Any]) -> Outcome:
    """Polars's outcome of `p` on one row: a value (doubles as codes) or the
    error it raises. One row at a time, so a column-wide error names its row."""
    frame = pl.DataFrame(
        {f"a{i}": [v] for i, v in enumerate(row)},
        schema={f"a{i}": TYPES[t][0] for i, t in enumerate(p.args)},
    )
    try:
        if ENGINE == "streaming":
            v = frame.lazy().select(_expr(p).alias("r")).collect(engine="streaming").item()
        else:
            v = frame.select(_expr(p).alias("r")).item()
    except BaseException as e:  # a Rust panic is a `PanicException`, a BaseException
        if isinstance(e, KeyboardInterrupt):
            raise
        return "error", f"{type(e).__name__}: {str(e).splitlines()[0]}"
    if isinstance(v, float):
        return "ok", encode_double(v)
    return "ok", v


def _same(a: Outcome, b: Outcome) -> bool:
    return a[0] == b[0] == "error" or a == b


def _show(o: Outcome, p: Probe) -> str:
    from sverify.contracts import decode_double

    v = o[1]
    if o[0] == "ok" and p.result == "float64" and isinstance(v, int):
        v = decode_double(v)
    return f"{o[0]} {v}"


def construct(p: Probe) -> str:
    """`p`'s expression with its argument types in place of the columns."""
    return p.construct.format(*(TYPES[t][0].__name__ for t in p.args))


#: Functions Lean evaluates on ASCII only: outside it they are black boxes
#: (`Text.upper`, Rust's `str::to_uppercase`), so the probe leaves those rows out.
ASCII_ONLY = {"upper", "lower"}


def _rows(p: Probe) -> list[tuple[Any, ...]]:
    rows = list(itertools.product(*(TYPES[t][1] for t in p.args)))
    if p.function in ASCII_ONLY:
        rows = [r for r in rows if all(v is None or v.isascii() for v in r)]
    return rows


def run_probe(p: Probe) -> Json:
    """`p`'s matching candidates, and for each candidate the rows that differ."""
    rows = _rows(p)
    engine = [polars_outcome(p, r) for r in rows]
    tried: dict[str, Json] = {}
    for cand in p.candidates or (None,):
        lean = lean_outcomes(p, rows, cand)
        diff = [
            {"row": str(list(r)), "polars": _show(e, p), "lean": _show(x, p)}
            for r, e, x in zip(rows, engine, lean, strict=True)
            if not _same(e, x)
        ]
        tried[cand or "(none)"] = {"differ": len(diff), "examples": diff[:4]}
    return {
        "construct": construct(p),
        "function": p.function,
        "option": p.option,
        "fixed": dict(p.fixed),
        "rows": len(rows),
        "matching": [c for c, t in tried.items() if t["differ"] == 0],
        "candidates": tried,
    }


def observe(o: Observation) -> Json:
    """`o`'s result, or the error it raises."""
    env = {"pl": pl, "math": math, "dt": dt, "Decimal": Decimal, "df": df, "bits": bits,
           "attempt": attempt,
           "inf": math.inf, "nan": math.nan}  # fmt: skip
    try:
        observed = repr(eval(o.code, env))
    except BaseException as e:
        if isinstance(e, KeyboardInterrupt):
            raise
        observed = f"error {type(e).__name__}: {str(e).splitlines()[0]}"
    return {"construct": o.construct, "area": o.area, "code": o.code, "observed": observed}


def probe_all(
    probes: Sequence[Probe] = PROBES,
    observations: Sequence[Observation] = OBSERVATIONS,
    log: Callable[[str], None] = print,
) -> list[Json]:
    found = []
    for p in probes:
        r = run_probe(p)
        log(f"{r['construct']} ({p.function}): {', '.join(r['matching']) or 'NO MATCH'}")
        found.append(r)
    for o in observations:
        r = observe(o)
        log(f"{o.construct}: {r['observed']}")
        found.append(r)
    return found


def _column_outcomes(
    p: Probe, rows: Sequence[Sequence[Any]], engine: Literal["in-memory", "streaming"]
) -> list[Outcome]:
    """`p` on all `rows` at once, each repeated so the frame has at least
    `TILE` rows (several morsels on streaming, and no length-1 column): one
    outcome per row, or the one error for all."""
    reps = -(-TILE // max(len(rows), 1))
    frame = pl.DataFrame(
        {f"a{i}": [r[i] for r in rows] * reps for i in range(len(p.args))},
        schema={f"a{i}": TYPES[t][0] for i, t in enumerate(p.args)},
    )
    try:
        out = frame.lazy().select(_expr(p).alias("r")).collect(engine=engine)["r"]
        values = out.to_list()[: len(rows)]
    except BaseException as e:
        if isinstance(e, KeyboardInterrupt):
            raise
        return [("error", f"{type(e).__name__}: {str(e).splitlines()[0]}")] * len(rows)
    return [("ok", encode_double(v)) if isinstance(v, float) else ("ok", v) for v in values]


#: The rows of a column-wide evaluation in `engine_diff`.
TILE = 6000


#: Observations for `engine_diff` alone: where the streaming engine's source
#: reads differently from the in-memory one's (facts polars-sum-float,
#: -var-std, -first-last, -sort-stability, -exec-when-eager,
#: -double-scalar-divisor, PL-3, PL-5). Big enough for several morsels.
STREAMING_OBSERVATIONS: list[Observation] = [
    _o("s-group-fsum-cancel", "aggregates",
       "df(g=[1] * 4, x=[1e16, 1.0, 1.0, -1e16]).group_by('g')"
       ".agg(pl.col('x').sum()).item(0, 'x')"),
    _o("s-group-fsum-f32", "aggregates",
       "df(g=[1] * 3, x=([16777216.0, 1.0, 1.0], pl.Float32)).group_by('g')"
       ".agg(pl.col('x').sum()).item(0, 'x')"),
    _o("s-group-mean-cancel", "aggregates",
       "df(g=[1] * 4, x=[1e16, 1.0, 1.0, -1e16]).group_by('g')"
       ".agg(pl.col('x').mean()).item(0, 'x')"),
    _o("s-group-var", "aggregates",
       "df(g=[1] * 4, x=[1e8 + 1, 1e8 + 2, 1e8 + 3, 1e8 + 4]).group_by('g')"
       ".agg(pl.col('x').var()).item(0, 'x')"),
    _o("s-fsum-runs", "aggregates",
       "sorted({repr(df(x=[(i * 0.1) % 7.3 - 3.1 for i in range(300_000)])"
       ".select(pl.col('x').sum()).item()) for _ in range(5)})"),
    _o("s-group-fsum-runs", "aggregates",
       "sorted({repr(df(g=[i % 3 for i in range(300_000)],"
       " x=[(i * 0.1) % 7.3 - 3.1 for i in range(300_000)]).group_by('g')"
       ".agg(pl.col('x').sum()).sort('g')['x'].to_list()) for _ in range(5)})"),
    _o("s-var-runs", "aggregates",
       "sorted({repr(df(x=[(i * 0.1) % 7.3 - 3.1 for i in range(300_000)])"
       ".select(pl.col('x').var()).item()) for _ in range(5)})"),
    _o("s-first-last-grouped", "aggregates",
       "df(g=[i % 7 for i in range(100_000)], i=range(100_000)).group_by('g')"
       ".agg(pl.col('i').first().alias('f'), pl.col('i').last().alias('l')).sort('g').rows()"),
    _o("s-implode-order", "aggregates",
       "all(x == sorted(x) for x in df(g=[i % 7 for i in range(100_000)], i=range(100_000))"
       ".group_by('g').agg(pl.col('i')).sort('g')['i'].to_list())"),
    _o("s-sort-ties-large", "relations",
       "(lambda s: all(a <= b for a, b in zip(s, s[1:])))("
       "df(k=[i % 3 for i in range(3_000_000)], i=range(3_000_000)).sort('k')"
       ".filter(pl.col('k') == 1)['i'].to_list())"),
    _o("s-group-order", "relations",
       "df(g=[(i * 7919) % 1000 for i in range(100_000)]).group_by('g').len()['g'].to_list()[:8]"),
    _o("s-when-masks-cast", "execution",
       "df(x=['1', 'a'] * 3000).select(pl.when(pl.col('x') == '1').then(pl.col('x').cast(pl.Int64))"
       ".otherwise(None)).to_series()[:2].to_list()"),
    _o("s-when-cse-cast", "execution",
       "df(x=['1', 'a'] * 3000).select("
       "pl.when(pl.col('x') == '1').then(pl.col('x').cast(pl.Int64) + 1).alias('a'),"
       " pl.when(pl.col('x') == '1').then(pl.col('x').cast(pl.Int64) + 2).alias('b'))"
       ".rows()[:2]"),
    # Lazy, so common-subexpression elimination runs (eager `select` skips it).
    _o("s-when-cse-lazy", "execution",
       "[attempt(lambda: pl.DataFrame({'x': ['1', 'a']}).lazy().select("
       "pl.when(pl.col('x') == '1').then(pl.col('x').cast(pl.Int64) + 1).alias('a'),"
       " pl.when(pl.col('x') == '1').then(pl.col('x').cast(pl.Int64) + 2).alias('b'))"
       ".collect(engine=e, optimizations=pl.QueryOptFlags(comm_subexpr_elim=c)).rows())"
       " for e in ('in-memory', 'streaming') for c in (True, False)]"),
    _o("s-and-eager-cast", "execution",
       "df(x=['a', '2'] * 3000).select((pl.col('x') != 'a') & (pl.col('x').cast(pl.Int64) > 1))"
       ".to_series()[:2].to_list()"),
    _o("s-coalesce-eager-cast", "execution",
       "df(x=['a', '2'] * 3000, y=[1, None] * 3000).select("
       "pl.coalesce(pl.col('y'), pl.col('x').cast(pl.Int64))).to_series()[:2].to_list()"),
    _o("s-filter-then-cast", "execution",
       "df(x=['a', '2'] * 3000).filter(pl.col('x') != 'a')"
       ".select(pl.col('x').cast(pl.Int64)).to_series()[:2].to_list()"),
    _o("s-scalar-divisor", "doubles",
       "df(x=[49.0, 0.0, 1e-300] * 3000).select((pl.col('x') % 49.0).alias('m'),"
       " (pl.col('x') // 49.0).alias('f'), (pl.col('x') / 1e-310).alias('d')).rows()[:3]"),
    _o("s-cov-decimal", "aggregates",
       "df(x=([Decimal('1.00'), Decimal('2.50'), Decimal('4.00')], pl.Decimal(10, 2)),"
       " y=([Decimal('1.00'), Decimal('2.00'), Decimal('4.50')], pl.Decimal(10, 2)))"
       ".select(pl.cov('x', 'y'), pl.corr('x', 'y').alias('c')).rows()"),
    _o("s-quantile-median", "aggregates",
       "df(g=[i % 3 for i in range(30_000)], x=[float(i % 101) for i in range(30_000)])"
       ".group_by('g').agg(pl.col('x').median().alias('m'),"
       " pl.col('x').quantile(0.3, 'linear').alias('q')).sort('g').rows()"),
]  # fmt: skip


def engine_diff(
    probes: Sequence[Probe] = PROBES,
    observations: Sequence[Observation] = (*OBSERVATIONS, *STREAMING_OBSERVATIONS),
    log: Callable[[str], None] = print,
) -> list[Json]:
    """Where the streaming engine differs from the in-memory one, without
    Lean: each probe one row at a time and column-wide (`TILE` rows), and
    each observation. One entry per probe or observation, with the rows or
    the values that differ (`differ` 0 where none does)."""
    global ENGINE
    found = []
    for p in probes:
        rows = _rows(p)
        ENGINE = "in-memory"
        mem = [polars_outcome(p, r) for r in rows]
        ENGINE = "streaming"
        stream = [polars_outcome(p, r) for r in rows]
        col_mem = _column_outcomes(p, rows, "in-memory")
        col_stream = _column_outcomes(p, rows, "streaming")
        diff = [
            {"row": str(list(r)), "how": how, "in-memory": _show(a, p), "streaming": _show(b, p)}
            for how, xs, ys in (("row", mem, stream), ("column", col_mem, col_stream))
            for r, a, b in zip(rows, xs, ys, strict=True)
            if not _same(a, b)
        ]
        # A column-wide value that differs from the same engine's one-row value.
        diff += [
            {"row": str(list(r)), "how": f"column vs row, {eng}", "row-wise": _show(a, p),
             "column-wise": _show(b, p)}
            for eng, xs, ys in (("in-memory", mem, col_mem), ("streaming", stream, col_stream))
            for r, a, b in zip(rows, xs, ys, strict=True)
            if b[0] == "ok" and not _same(a, b)
        ]  # fmt: skip
        log(f"{construct(p)}: {len(diff)} differ")
        found.append({"construct": construct(p), "function": p.function, "rows": len(rows),
                      "differ": len(diff), "examples": diff[:6]})  # fmt: skip
    for o in observations:
        ENGINE = "in-memory"
        a = observe(o)["observed"]
        ENGINE = "streaming"
        b = observe(o)["observed"]
        log(f"{o.construct}: {'same' if a == b else 'DIFFERS'}")
        found.append({"construct": o.construct, "area": o.area, "code": o.code,
                      "differ": int(a != b), "in-memory": a, "streaming": b})  # fmt: skip
    ENGINE = "in-memory"
    return found


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--write", action="store_true", help="write probes.json")
    parser.add_argument(
        "--engine", choices=("in-memory", "streaming"), default="in-memory",
        help="the engine to run the probes on",
    )  # fmt: skip
    parser.add_argument(
        "--diff", action="store_true",
        help="compare streaming with in-memory, without Lean (writes probes-streaming.json)",
    )  # fmt: skip
    args = parser.parse_args(argv)
    global ENGINE
    if args.diff:
        found = engine_diff()
        if args.write:
            doc = {"polars": pl.__version__, "engine": "streaming vs in-memory", "probes": found}
            OUT_STREAMING.write_text(json.dumps(doc, indent=1) + "\n")
            print(f"-> {OUT_STREAMING}")
        return
    ENGINE = args.engine
    found = probe_all()
    if args.write and ENGINE == "in-memory":
        OUT.write_text(json.dumps({"polars": pl.__version__, "probes": found}, indent=1) + "\n")
        print(f"-> {OUT}")


if __name__ == "__main__":
    main()

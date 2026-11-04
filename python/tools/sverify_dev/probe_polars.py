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
`tests/test_probe_polars.py` checks it is current.
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
from typing import Any

import polars as pl

from sverify_dev.probe import Outcome, Probe, encode_double, lean_outcomes

Json = dict[str, Any]

OUT = Path(__file__).resolve().parents[3] / "characterization" / "polars" / "probes.json"


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
]  # fmt: skip


@dataclass(frozen=True)
class Observation:
    """A Polars program and what it gives."""

    construct: str
    """Its name, which facts cite."""
    area: str
    code: str
    """A Python expression over `pl`, `math`, `dt`, `Decimal`, `df`, `bits`, `inf`
    and `nan`."""


def _o(construct: str, area: str, code: str) -> Observation:
    return Observation(construct, area, code)


def df(**cols: Any) -> pl.DataFrame:
    """A frame of the given columns (`df(x=[...])`), each a list or a
    `(list, dtype)` pair."""
    return pl.DataFrame(
        {k: v[0] if isinstance(v, tuple) else v for k, v in cols.items()},
        schema_overrides={k: v[1] for k, v in cols.items() if isinstance(v, tuple)},
    )


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
]  # fmt: skip


def bits(x: float) -> str:
    """A double's bits, in hex."""
    return hex(struct.unpack("<Q", struct.pack("<d", x))[0])


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


def run_probe(p: Probe) -> Json:
    """`p`'s matching candidates, and for each candidate the rows that differ."""
    rows = list(itertools.product(*(TYPES[t][1] for t in p.args)))
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


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--write", action="store_true", help="write probes.json")
    args = parser.parse_args(argv)
    found = probe_all()
    if args.write:
        OUT.write_text(json.dumps({"polars": pl.__version__, "probes": found}, indent=1) + "\n")
        print(f"-> {OUT}")


if __name__ == "__main__":
    main()

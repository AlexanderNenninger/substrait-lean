"""Probe each engine's statistical aggregates of doubles (#918 Part B, D30).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API. The facts on `stat_algo`, `stat_degenerate`, `quantile_interp` and a
window's `null_order` cite it.

One set of cases, written once in SQL that DuckDB, Spark and Snowflake all
read, and once as Polars expressions:

- `shift-<s>`: VAR_*, STDDEV_*, COVAR_*(x, 2x) and CORR(x, 2x) of
  {4, 7, 13, 16} + s, for s in 0, 1e6, 1e8, 1e9 and 1e12. The true values are
  VAR_SAMP 30, VAR_POP 22.5, COVAR_SAMP 60, COVAR_POP 45 and CORR 1, at every
  shift, and every input is a double exactly. Welford, Chan and two-pass stay
  exact; the textbook formula `(Σx² − (Σx)²/n) / (n − 1)` gives 29.33 at 1e8
  and 0 at 1e9.
- `negative-<x>`: VAR_POP of one value repeated (the true value is 0), where
  the textbook formula in doubles is negative. Welford's updates never are.
- `n0`, `n1`: the sample-size rule with no values and with one.
- `nan`, `inf`, `neginf`, `infs`: VAR and STDDEV with NaN or ±inf inputs.
- `corr-const`, `corr-const-both`: CORR where one variance or both are 0.
- `quantile`: PERCENTILE_CONT(0.3) of 0.4 and 1.697 (linear at (n − 1)·p), whose
  value in doubles differs from the exact interpolation rounded once.
- `window-null-order` (SQL only): LAG and ROW_NUMBER over `ORDER BY k` and
  `ORDER BY k DESC` without NULLS FIRST or LAST, k = 1, NULL, 2.

    python -m sverify_dev.probe_statistics [--spark] [--print-sql]

prints one JSON object: the expected values, and per engine and path each
case's row (DuckDB's SQL; Polars' streaming engine, ungrouped and grouped,
whose algorithms differ). `--spark` adds a local Spark session (a JVM, Java 17
or 21; about half a minute). `--print-sql` prints the cases' SQL as JSON and
runs nothing, for an engine probed elsewhere.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction
from typing import Any

BASE = [4.0, 7.0, 13.0, 16.0]
SHIFTS = [0.0, 1e6, 1e8, 1e9, 1e12]
#: Values whose repeats give a negative VAR_POP under the textbook formula.
NEGATIVE = {"0.1": [0.1] * 3, "0.3": [0.3] * 5, "1e8+0.1": [1e8 + 0.1] * 5}
QUANTILE_P = 0.3
QUANTILE_VALUES = [0.4, 1.697]

MOMENTS = ["var_samp", "var_pop", "stddev_samp", "stddev_pop", "covar_samp", "covar_pop", "corr"]
EXPECTED_SHIFT = {
    "var_samp": 30.0,
    "var_pop": 22.5,
    "stddev_samp": math.sqrt(30.0),
    "stddev_pop": math.sqrt(22.5),
    "covar_samp": 60.0,
    "covar_pop": 45.0,
    "corr": 1.0,
}


def _lit(v: float | None) -> str:
    if v is None:
        return "CAST(NULL AS DOUBLE)"
    if math.isnan(v):
        return "CAST('NaN' AS DOUBLE)"
    if math.isinf(v):
        return "CAST('Infinity' AS DOUBLE)" if v > 0 else "CAST('-Infinity' AS DOUBLE)"
    return f"CAST({v!r} AS DOUBLE)"


def _values(cols: list[list[float | None]], names: str) -> str:
    rows = ", ".join("(" + ", ".join(_lit(v) for v in row) + ")" for row in zip(*cols, strict=True))
    return f"(VALUES {rows}) AS t({names})"


def _moments_sql(xs: list[float | None], ys: list[float | None]) -> str:
    cols = ", ".join(
        f"{f}(x) AS {f}" if not f.startswith(("covar", "corr")) else f"{f}(x, y) AS {f}"
        for f in MOMENTS
    )
    return f"SELECT {cols} FROM {_values([xs, ys], 'x, y')}"


Column = list[float | None]


def cases() -> dict[str, tuple[Column, Column]]:
    """Each case's (x, y) columns for the moment aggregates."""
    out: dict[str, tuple[Column, Column]] = {}
    for s in SHIFTS:
        xs: Column = [s + b for b in BASE]
        out[f"shift-{s:g}"] = (xs, [2 * s + 2 * b for b in BASE])
    for name, vs in NEGATIVE.items():
        out[f"negative-{name}"] = (list(vs), list(vs))
    out["n0"] = ([None], [None])
    out["n1"] = ([3.0], [6.0])
    out["nan"] = ([1.0, math.nan, 2.0], [1.0, 2.0, 3.0])
    out["inf"] = ([1.0, math.inf, 2.0], [1.0, 2.0, 3.0])
    out["neginf"] = ([1.0, -math.inf, 2.0], [1.0, 2.0, 3.0])
    out["infs"] = ([math.inf, math.inf], [1.0, 2.0])
    out["corr-const"] = ([1.0, 2.0, 3.0], [5.0, 5.0, 5.0])
    out["corr-const-both"] = ([5.0, 5.0], [5.0, 5.0])
    return out


QUANTILE_SQL = (
    f"SELECT percentile_cont({QUANTILE_P}) WITHIN GROUP (ORDER BY x) AS q "
    f"FROM {_values([list(QUANTILE_VALUES)], 'x')}"
)
_K = _values([[1.0, None, 2.0], [0.0, 1.0, 2.0]], "k, i")
WINDOW_SQL = (
    "SELECT i, k, lag(k) OVER (ORDER BY k, i) AS lag_asc, "
    "row_number() OVER (ORDER BY k, i) AS rn_asc, "
    "lag(k) OVER (ORDER BY k DESC, i) AS lag_desc, "
    "row_number() OVER (ORDER BY k DESC, i) AS rn_desc "
    f"FROM {_K} ORDER BY i"
)


def sql_cases() -> dict[str, str]:
    """Every SQL case, by name."""
    out = {name: _moments_sql(xs, ys) for name, (xs, ys) in cases().items()}
    out["quantile"] = QUANTILE_SQL
    out["window-null-order"] = WINDOW_SQL
    return out


def expected() -> dict[str, Any]:
    """The true values the probe compares against."""
    lo, hi = (Fraction(v) for v in QUANTILE_VALUES)
    pos = Fraction(QUANTILE_P) * (len(QUANTILE_VALUES) - 1)
    exact_q = float(lo + (hi - lo) * pos)
    d = (len(QUANTILE_VALUES) - 1) * QUANTILE_P
    return {
        "shift": EXPECTED_SHIFT,
        "negative": "var_pop 0.0: Welford and two-pass are >= 0; the textbook formula is negative",
        "quantile": {
            "exact_rounded_once": exact_q,
            "lo*(1-d)+hi*d": QUANTILE_VALUES[0] * (1 - d) + QUANTILE_VALUES[1] * d,
            "lo+(hi-lo)*d": QUANTILE_VALUES[0] + (QUANTILE_VALUES[1] - QUANTILE_VALUES[0]) * d,
        },
        "window-null-order": "NULLS_FIRST ascending: row_number of k = NULL is 1 in rn_asc",
    }


def _clean(v: Any) -> Any:
    if isinstance(v, float) and math.isnan(v):
        return "NaN"
    if isinstance(v, float) and math.isinf(v):
        return "inf" if v > 0 else "-inf"
    return v


def _rows(rows: list[Any], names: list[str]) -> Any:
    """One row as a dict of its columns; several rows as a list of them."""
    out = [{n: _clean(v) for n, v in zip(names, r, strict=True)} for r in rows]
    return out[0] if len(out) == 1 else out


def _dump(found: Any, indent: str = "") -> str:
    """JSON with one line per case: a dict is spread over lines while it holds a dict."""
    if isinstance(found, dict) and any(isinstance(v, dict) for v in found.values()):
        inner = ",\n".join(
            f"{indent}  {json.dumps(k)}: {_dump(v, indent + '  ')}" for k, v in found.items()
        )
        return "{\n" + inner + "\n" + indent + "}"
    return json.dumps(found)


def duckdb_cases() -> dict[str, Any]:
    import duckdb

    con = duckdb.connect()
    out: dict[str, Any] = {}
    for name, sql in sql_cases().items():
        cur = con.execute(sql)
        out[name] = _rows(cur.fetchall(), [d[0] for d in cur.description])
    return out


def polars_cases() -> dict[str, Any]:
    import polars as pl

    def moments() -> list[pl.Expr]:
        x, y = pl.col("x"), pl.col("y")
        return [
            x.var(ddof=1).alias("var_samp"),
            x.var(ddof=0).alias("var_pop"),
            x.std(ddof=1).alias("stddev_samp"),
            x.std(ddof=0).alias("stddev_pop"),
            pl.cov(x, y, ddof=1).alias("covar_samp"),
            pl.cov(x, y, ddof=0).alias("covar_pop"),
            pl.corr(x, y).alias("corr"),
        ]

    out: dict[str, Any] = {}
    for path in ("ungrouped", "grouped"):
        found: dict[str, Any] = {}
        for name, (xs, ys) in cases().items():
            lf = pl.LazyFrame(
                {"g": [0] * len(xs), "x": xs, "y": ys},
                schema={"g": pl.Int64, "x": pl.Float64, "y": pl.Float64},
            )
            q = (
                lf.select(moments())
                if path == "ungrouped"
                else lf.group_by("g").agg(moments()).drop("g")
            )
            df = q.collect(engine="streaming")
            found[name] = _rows(df.rows(), df.columns)
        lf = pl.LazyFrame({"g": [0, 0], "x": QUANTILE_VALUES})
        qe = pl.col("x").quantile(QUANTILE_P, "linear").alias("q")
        q = lf.select(qe) if path == "ungrouped" else lf.group_by("g").agg(qe).drop("g")
        df = q.collect(engine="streaming")
        found["quantile"] = _rows(df.rows(), df.columns)
        out[path] = found
    return out


def spark_cases() -> dict[str, Any]:
    from pyspark.sql import SparkSession

    spark = SparkSession.builder.master("local[2]").getOrCreate()
    out: dict[str, Any] = {}
    for ansi in ("true", "false"):
        spark.conf.set("spark.sql.ansi.enabled", ansi)
        found: dict[str, Any] = {}
        for name, sql in sql_cases().items():
            df = spark.sql(sql)
            found[name] = _rows([tuple(r) for r in df.collect()], df.columns)
        out[f"ansi={ansi}"] = found
    spark.stop()
    return out


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--spark", action="store_true", help="also probe a local Spark session")
    parser.add_argument(
        "--print-sql", action="store_true", help="print the SQL cases and run nothing"
    )
    args = parser.parse_args(argv)
    if args.print_sql:
        found: dict[str, Any] = sql_cases()
    else:
        found = {"expected": expected(), "duckdb": duckdb_cases(), "polars": polars_cases()}
        if args.spark:
            found["spark"] = spark_cases()
    sys.stdout.write(_dump(found) + "\n")


if __name__ == "__main__":
    main()

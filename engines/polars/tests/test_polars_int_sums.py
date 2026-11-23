"""Polars's `sum` and `mean` of integer-valued doubles are exact under the
streaming engine (D35, amended 2026-11-19), over several chunks
(`_int_sums.py`)."""

import polars as pl
import pytest

from _int_sums import cases, check

CASES = cases()


@pytest.mark.parametrize(("name", "values"), CASES, ids=[n for n, _ in CASES])
def test_sum_and_mean_are_exact_when_streaming(name, values):
    step = max(1, len(values) // 7)
    chunks = [
        pl.DataFrame({"x": [float(v) for v in values[i : i + step]]}, schema={"x": pl.Float64})
        for i in range(0, len(values), step)
    ]
    df = pl.concat(chunks, rechunk=False)
    out = df.lazy().select(s=pl.col("x").sum(), m=pl.col("x").mean()).collect(engine="streaming")
    check(values, out["s"][0], out["m"][0])


@pytest.mark.parametrize(("name", "values"), CASES, ids=[n for n, _ in CASES])
def test_grouped_sum_and_mean_are_exact_in_memory(name, values):
    # The in-memory engine, which sverify does not run, sums a group by Kahan's sum
    # (polars-sum-float): exact here too.
    df = pl.DataFrame(
        {"g": [1] * len(values), "x": [float(v) for v in values]},
        schema={"g": pl.Int64, "x": pl.Float64},
    )
    out = df.group_by("g").agg(s=pl.col("x").sum(), m=pl.col("x").mean())
    check(values, out["s"][0], out["m"][0])

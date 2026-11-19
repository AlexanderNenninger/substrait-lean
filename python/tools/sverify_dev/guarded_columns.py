"""Engine probes P1 and P2 of #1719 (D50-d, guarded columns).

A guarded chain is a stack of projections. Projection i appends two columns
over the previous ones:

    r_i := r_{i-1} AND (c_{i-1} IS NULL OR c_{i-1})    -- the reach
    c_i := CASE WHEN r_i THEN p_i END                   -- r_i written out

The operator above reads the plain `c_1 AND ... AND c_k`. The design needs two
things of an engine:

P1, laziness. `p_i` is evaluated on no row where `r_i` is FALSE, with the
    optimizer on, also under a selective filter above, over an aggregate, and
    where the optimizer can fold the reach to FALSE. `p_i` raises on the rows
    that must not reach it (a strict cast of the text 'bad').
P2, no inlining. Each level reads the previous reach twice, so an optimizer that
    merges projections by substitution rebuilds a tree of 2^k copies. The plan's
    text, the planning and running time and the peak memory grow linearly in k.

    python -m sverify_dev.guarded_columns p1 --engine duckdb|polars|spark
    python -m sverify_dev.guarded_columns p2 --engine ... [--levels 5 10 20 40]

Each prints one JSON document. `p2` runs every level count in a child process
under a timeout and a memory watchdog. Run Spark and large levels on homelab
(`homelab-run`).
"""

from __future__ import annotations

import argparse
import json
import os
import resource
import subprocess
import sys
import time
from collections.abc import Callable
from typing import Any

N = 3000
BAD = "bad"


def rows(kind: str) -> list[tuple[int, str]]:
    """`mixed`: every third row is the text that a strict cast rejects."""
    if kind == "allbad":
        return [(i, BAD) for i in range(1, N + 1)]
    return [(i, BAD if i % 3 == 0 else str(i)) for i in range(1, N + 1)]


# --- a case: what the chain reads and what is put above it --------------------

# reach1: how r_1 is written. `notnull` (id IS NOT NULL, TRUE on every row and
# opaque to the optimizer), `const` (1 = 0, folds to FALSE), `data` (s IS NULL
# AND s IS NOT NULL, FALSE on every row but a rewrite is needed to see it).
# p: the operand of levels 2..k. `cast` (CAST(s AS INT) > 0, raises on `bad`),
# `const_bad` (CAST('bad' AS INT) > 0, raises wherever it is evaluated, also at
# plan time when folded).
CASES: dict[str, dict[str, Any]] = {
    "plain": dict(reach1="notnull", p="cast", data="mixed", above="none"),
    "filter_id": dict(reach1="notnull", p="cast", data="mixed", above="id"),
    "filter_chain": dict(reach1="notnull", p="cast", data="mixed", above="value"),
    "aggregate": dict(reach1="notnull", p="cast", data="mixed", above="agg"),
    "folded_const": dict(reach1="const", p="const_bad", data="mixed", above="none"),
    "folded_data": dict(reach1="data", p="cast", data="allbad", above="none"),
    "folded_const_filter": dict(reach1="const", p="const_bad", data="mixed", above="id"),
    "const_operand": dict(reach1="data", p="const_bad", data="allbad", above="none"),
    "const_in_column_operand": dict(reach1="notnull", p="col_gt_bad", data="allbad", above="none"),
    "const_operand_column_reach": dict(
        reach1="notnull", p="const_bad", data="allbad", above="none"
    ),
}
LEVELS_P1 = 4


def expected(case: dict[str, Any], levels: int) -> Any:
    """The reference value of the chain's reading, computed in Python."""
    data = rows(case["data"])
    vals: dict[int, bool | None] = {}
    for i, s in data:
        if case["reach1"] in ("const", "data"):
            vals[i] = None  # every column is NULL: nothing was reached
        else:
            vals[i] = s != BAD  # c_1 FALSE ends the chain: FALSE
    above = case["above"]
    if above == "id":
        vals = {i: v for i, v in vals.items() if i < 10}
    if above == "value":
        vals = {i: v for i, v in vals.items() if v}
    if above == "agg":
        return sum(1 for v in vals.values() if v)
    return sorted(vals.items(), key=lambda kv: kv[0])


# --- SQL chain (DuckDB, Spark) -------------------------------------------------


def _reach1_sql(kind: str) -> str:
    return {
        "notnull": "id IS NOT NULL",
        "const": "(1 = 0)",
        "data": "(s IS NULL AND s IS NOT NULL)",
    }[kind]


def _p_sql(kind: str) -> str:
    return {
        "cast": "CAST(s AS INT) > 0",
        "const_bad": f"CAST('{BAD}' AS INT) > 0",
        "col_gt_bad": f"CAST(id AS INT) > CAST('{BAD}' AS INT)",
    }[kind]


def sql_chain(case: dict[str, Any], levels: int, table: str = "t") -> str:
    q = f"SELECT id, s FROM {table}"
    q = (
        f"SELECT *, {_reach1_sql(case['reach1'])} AS r1, "
        f"CASE WHEN {_reach1_sql(case['reach1'])} THEN s <> '{BAD}' END AS c1 FROM ({q})"
    )
    for i in range(2, levels + 1):
        reach = f"(r{i - 1} AND (c{i - 1} IS NULL OR c{i - 1}))"
        c = f"CASE WHEN {reach} THEN {_p_sql(case['p'])} END"
        q = f"SELECT *, {reach} AS r{i}, {c} AS c{i} FROM ({q})"
    reading = " AND ".join(f"c{i}" for i in range(1, levels + 1))
    q = f"SELECT id, {reading} AS v FROM ({q})"
    above = case["above"]
    if above == "id":
        q = f"SELECT id, v FROM ({q}) WHERE id < 10"
    elif above == "value":
        q = f"SELECT id, v FROM ({q}) WHERE v"
    elif above == "agg":
        q = f"SELECT sum(CASE WHEN v THEN 1 ELSE 0 END) AS n FROM ({q})"
    return q


def _norm(result: list[tuple], case: dict[str, Any]) -> Any:
    if case["above"] == "agg":
        return int(result[0][0] or 0)
    return sorted(((int(a), b) for a, b in result), key=lambda kv: kv[0])


# --- engines ------------------------------------------------------------------


def duckdb_engine() -> dict[str, Any]:
    import duckdb

    def run(case: dict[str, Any], levels: int, *, plan_only: bool = False) -> dict[str, Any]:
        con = duckdb.connect()
        con.execute("CREATE TABLE t(id BIGINT, s VARCHAR)")
        con.executemany("INSERT INTO t VALUES (?, ?)", rows(case["data"]))
        q = sql_chain(case, levels)
        t0 = time.perf_counter()
        plan = con.execute("EXPLAIN " + q).fetchall()
        plan_s = time.perf_counter() - t0
        plan_text = "\n".join(str(c) for r in plan for c in r)
        out: dict[str, Any] = {"plan_chars": len(plan_text), "plan_s": round(plan_s, 3)}
        if plan_only:
            return out
        t0 = time.perf_counter()
        res = con.execute(q).fetchall()
        out["run_s"] = round(time.perf_counter() - t0, 3)
        out["result"] = _norm(res, case)
        return out

    return {"run": run, "version": duckdb.__version__}


def polars_engine() -> dict[str, Any]:
    import polars as pl

    def reach1(kind: str) -> pl.Expr:
        return {
            "notnull": pl.col("id").is_not_null(),
            "const": pl.lit(1) == pl.lit(0),
            "data": pl.col("s").is_null() & pl.col("s").is_not_null(),
        }[kind]

    def p(kind: str) -> pl.Expr:
        return {
            "cast": pl.col("s").cast(pl.Int64, strict=True) > 0,
            "const_bad": pl.lit(BAD).cast(pl.Int64, strict=True) > 0,
            "col_gt_bad": pl.col("id").cast(pl.Int64) > pl.lit(BAD).cast(pl.Int64, strict=True),
        }[kind]

    def build(case: dict[str, Any], levels: int) -> pl.LazyFrame:
        data = rows(case["data"])
        lf = pl.LazyFrame({"id": [a for a, _ in data], "s": [b for _, b in data]})
        r1 = reach1(case["reach1"])
        lf = lf.with_columns(
            r1.alias("r1"),
            pl.when(r1).then(pl.col("s") != BAD).otherwise(None).alias("c1"),
        )
        for i in range(2, levels + 1):
            rp, cp = pl.col(f"r{i - 1}"), pl.col(f"c{i - 1}")
            reach = rp & (cp.is_null() | cp)
            lf = lf.with_columns(
                reach.alias(f"r{i}"),
                pl.when(reach).then(p(case["p"])).otherwise(None).alias(f"c{i}"),
            )
        v = pl.col("c1")
        for i in range(2, levels + 1):
            v = v & pl.col(f"c{i}")
        lf = lf.select("id", v.alias("v"))
        above = case["above"]
        if above == "id":
            lf = lf.filter(pl.col("id") < 10)
        elif above == "value":
            lf = lf.filter(pl.col("v"))
        elif above == "agg":
            lf = lf.select(pl.col("v").cast(pl.Int64).sum().alias("n"))
        return lf

    def run(case: dict[str, Any], levels: int, *, plan_only: bool = False) -> dict[str, Any]:
        t0 = time.perf_counter()
        lf = build(case, levels)
        plan_text = lf.explain()
        plan_s = time.perf_counter() - t0
        out: dict[str, Any] = {"plan_chars": len(plan_text), "plan_s": round(plan_s, 3)}
        if plan_only:
            return out
        t0 = time.perf_counter()
        df = lf.collect(engine="streaming")
        out["run_s"] = round(time.perf_counter() - t0, 3)
        out["result"] = _norm(df.rows(), case)
        return out

    return {"run": run, "version": pl.__version__}


def spark_engine() -> dict[str, Any]:
    import pyspark
    from pyspark.sql import SparkSession

    spark = (
        SparkSession.builder.master("local[2]")
        .config("spark.sql.ansi.enabled", "true")
        .config("spark.sql.shuffle.partitions", "2")
        .config("spark.ui.enabled", "false")
        .getOrCreate()
    )

    def run(case: dict[str, Any], levels: int, *, plan_only: bool = False) -> dict[str, Any]:
        df0 = spark.createDataFrame(rows(case["data"]), "id BIGINT, s STRING").repartition(2)
        df0.createOrReplaceTempView("t")
        t0 = time.perf_counter()
        df = spark.sql(sql_chain(case, levels))
        plan_text = df._jdf.queryExecution().optimizedPlan().toString()  # pyrefly: ignore
        plan_s = time.perf_counter() - t0
        out: dict[str, Any] = {"plan_chars": len(plan_text), "plan_s": round(plan_s, 3)}
        if plan_only:
            return out
        t0 = time.perf_counter()
        res = [tuple(r) for r in df.collect()]
        out["run_s"] = round(time.perf_counter() - t0, 3)
        out["result"] = _norm(res, case)
        return out

    return {"run": run, "version": pyspark.__version__}


ENGINES: dict[str, Callable[[], dict[str, Any]]] = {
    f.__name__.removesuffix("_engine"): f for f in (duckdb_engine, polars_engine, spark_engine)
}


# --- P1 ------------------------------------------------------------------------


def _control(engine: str) -> dict[str, Any]:
    """An unguarded cast of the bad text must raise: the probe can see a raise."""
    try:
        if engine == "polars":
            import polars as pl

            pl.LazyFrame({"s": [BAD]}).select(pl.col("s").cast(pl.Int64, strict=True)).collect(
                engine="streaming"
            )
        elif engine == "duckdb":
            import duckdb

            duckdb.connect().execute(f"SELECT CAST('{BAD}' AS INT)").fetchall()
        else:
            from pyspark.sql import SparkSession

            SparkSession.builder.getOrCreate().sql(f"SELECT CAST('{BAD}' AS INT)").collect()
    except Exception as e:
        return {"raised": True, "error": type(e).__name__}
    return {"raised": False}


def p1(engine: str) -> dict[str, Any]:
    eng = ENGINES[engine]()
    out: dict[str, Any] = {
        "probe": "P1",
        "engine": engine,
        "version": eng["version"],
        "levels": LEVELS_P1,
        "cases": {},
    }
    out["control_unguarded_cast"] = _control(engine)
    for name, case in CASES.items():
        try:
            got = eng["run"](case, LEVELS_P1)
            ok = got["result"] == expected(case, LEVELS_P1)
            out["cases"][name] = {
                "raised": False,
                "result_matches": ok,
                "plan_chars": got["plan_chars"],
            }
        except Exception as e:  # the engine raised: P1 fails here
            out["cases"][name] = {"raised": True, "error": f"{type(e).__name__}: {str(e)[:160]}"}
    out["pass"] = all((not c["raised"]) and c["result_matches"] for c in out["cases"].values())
    return out


# --- P2 ------------------------------------------------------------------------


def _child(engine: str, levels: int, mode: str) -> None:
    eng = ENGINES[engine]()
    case = CASES["plain"]
    got = eng["run"](case, levels, plan_only=(mode == "plan"))
    if mode == "run":
        got["result_matches"] = got.pop("result") == expected(case, levels)
    usage = resource.getrusage(resource.RUSAGE_SELF)
    scale = 1 if sys.platform == "darwin" else 1024  # ru_maxrss: bytes on macOS, KiB on Linux
    got["child_peak_rss_mb"] = round(usage.ru_maxrss * scale / 2**20)
    print(json.dumps(got))


def _spawn(engine: str, levels: int, mode: str, timeout: float, rss_cap_mb: int) -> dict[str, Any]:
    """Run one level count in a child; kill it past the timeout or the memory cap."""
    import psutil

    cmd = [
        sys.executable,
        "-m",
        "sverify_dev.guarded_columns",
        "child",
        "--engine",
        engine,
        "--levels",
        str(levels),
        "--mode",
        mode,
    ]
    t0 = time.perf_counter()
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    peak = 0
    why = None
    while proc.poll() is None:
        try:
            ps = psutil.Process(proc.pid)
            rss = ps.memory_info().rss + sum(
                c.memory_info().rss for c in ps.children(recursive=True)
            )
        except psutil.Error:
            rss = 0
        peak = max(peak, rss)
        if rss > rss_cap_mb * 2**20:
            why = f"killed: rss over {rss_cap_mb} MB"
        elif time.perf_counter() - t0 > timeout:
            why = f"killed: over {timeout:.0f} s"
        if why:
            try:
                for c in psutil.Process(proc.pid).children(recursive=True):
                    c.kill()
            except psutil.Error:
                pass
            proc.kill()
            break
        time.sleep(0.05)
    stdout, stderr = proc.communicate()
    res: dict[str, Any] = {
        "levels": levels,
        "mode": mode,
        "wall_s": round(time.perf_counter() - t0, 2),
        "peak_rss_mb": round(peak / 2**20),
    }
    if why:
        res["error"] = why
    elif proc.returncode != 0:
        tail = stderr.strip().splitlines()
        res["error"] = f"exit {proc.returncode}: {tail[-1][:200] if tail else ''}"
    else:
        res.update(json.loads(stdout.strip().splitlines()[-1]))
    return res


def p2(engine: str, levels: list[int], timeout: float, rss_cap_mb: int) -> dict[str, Any]:
    eng = ENGINES[engine]()
    out: dict[str, Any] = {
        "probe": "P2",
        "engine": engine,
        "version": eng["version"],
        "timeout_s": timeout,
        "rss_cap_mb": rss_cap_mb,
        "plan": [],
        "run": [],
    }
    for mode in ("plan", "run"):
        for k in levels:
            r = _spawn(engine, k, mode, timeout, rss_cap_mb)
            out[mode].append(r)
            print(json.dumps(r), file=sys.stderr, flush=True)
            if "error" in r:
                break  # past the cap or the timeout: larger levels are no news
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("what", choices=["p1", "p2", "child"])
    ap.add_argument("--engine", required=True, choices=sorted(ENGINES))
    ap.add_argument("--levels", type=int, nargs="+", default=[5, 10, 20, 40])
    ap.add_argument("--timeout", type=float, default=300.0)
    ap.add_argument("--rss-cap-mb", type=int, default=6000)
    ap.add_argument("--mode", choices=["plan", "run"], default="run")
    a = ap.parse_args()
    if a.what == "child":
        _child(a.engine, a.levels[0], a.mode)
        return
    os.environ.setdefault("PYTHONWARNINGS", "ignore")
    res = p1(a.engine) if a.what == "p1" else p2(a.engine, a.levels, a.timeout, a.rss_cap_mb)
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    main()

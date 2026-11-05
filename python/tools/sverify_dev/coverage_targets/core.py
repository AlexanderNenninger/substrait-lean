"""Core: logic, comparisons, NULLs, arithmetic, math, decimals (`sql_lift/core.py`)."""

from __future__ import annotations

from sverify_dev.coverage_targets._common import target

AREA = "core"

TARGETS = [
    target(
        AREA,
        "arithmetic, CASE, COALESCE, NULLIF, comparisons",
        "in",
        "catalogue: arithmetic_float 26, case_when 14, coalesce_nullif 6, between 11",
        True,
        sql="SELECT qty / NULLIF(id, 0), coalesce(name, '?'), greatest(qty, id), "
        "CASE WHEN qty > 0 THEN 'pos' ELSE 'other' END, qty IS DISTINCT FROM id FROM t",
    ),
    target(
        AREA,
        "math functions",
        "in",
        "catalogue: math_funcs 5, math_transcendental 2",
        True,
        sql="SELECT qty // 2, qty % 3, abs(amount), sqrt(abs(amount)), ln(abs(amount) + 1), "
        "power(amount, 2), round(amount, 2) FROM t",
    ),
    target(
        AREA,
        "decimal arithmetic and aggregates",
        "in",
        "catalogue: decimal 40 (TPC-H, TPC-DS, finance); double-entry pattern (#749)",
        True,
        sql="SELECT sum(price * qty), avg(price), min(price), max(price), max(price) / 3 FROM t",
    ),
    target(
        AREA,
        "round of a decimal",
        "in",
        "money rounding: round(price * 1.19, 2); replay 28",
        False,
        sql="SELECT round(price * 1.19, 2) FROM t",
        issue=27,
    ),
    target(
        AREA,
        "DuckDB aliases: if, iff, len, substr, arbitrary",
        "in",
        "DuckDB style SQL; replay (binder tests)",
        False,
        sql="SELECT if(flag, 1, 0), substr(name, 2) FROM t",
        issue=328,
    ),
    target(
        AREA,
        "fp32 (FLOAT)",
        "skipped",
        "replay 427; Parquet files written by ML tools",
        False,
        sql="SELECT CAST(amount AS FLOAT) FROM t",
        issue=417,
        why="the model computes in binary64; rounding to binary32 after each step needs a model "
        "of its own. Cast FLOAT columns to DOUBLE at the source",
    ),
    target(
        AREA,
        "now, current_date, random, uuid",
        "skipped",
        "Ibis now, today, random, uuid",
        False,
        sql="SELECT current_date FROM t",
        ibis="now",
        issue=58,
        why="another value on every run, so no proof covers it; pass the date in as a value "
        "(dynamic parameters, #354)",
    ),
    target(
        AREA,
        "unsigned integers and HUGEINT",
        "after",
        "replay 1,495, mostly DuckDB's own type tests",
        False,
        sql="SELECT CAST(qty AS UINTEGER) FROM t",
        issue=350,
    ),
    target(
        AREA,
        "printf, format, signbit",
        "in",
        "labels, zero-padded codes; replay 80",
        True,
        sql="SELECT printf('%05d', qty), signbit(amount) FROM t",
    ),
    target(
        AREA,
        "age, base64, octet_length and other scalars",
        "after",
        "replay ~60",
        False,
        sql="SELECT age(ts, ts) FROM t",
        issue=328,
    ),
]

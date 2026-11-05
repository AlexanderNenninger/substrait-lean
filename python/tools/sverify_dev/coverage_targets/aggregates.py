"""Aggregates (`sql_lift/_base.py`'s `_AGGREGATES`)."""

from __future__ import annotations

from sverify_dev.coverage_targets._common import target

AREA = "aggregates"

TARGETS = [
    target(
        AREA,
        "sum, count, avg, min, max, count distinct, FILTER",
        "in",
        "catalogue: sum 57, count 28, min_max 20, avg 19, agg_filter 10, count_distinct 8",
        True,
        sql="SELECT sum(qty), count(*), avg(amount), min(amount), max(ts), count(DISTINCT name), "
        "count(*) FILTER (WHERE flag) FROM t",
    ),
    target(
        AREA,
        "stddev, variance, corr",
        "in",
        "catalogue: stddev_var 4, corr 1; float pattern (#749)",
        True,
        sql="SELECT stddev_samp(amount), var_pop(amount), corr(amount, qty) FROM t",
    ),
    target(
        AREA,
        "median, quantile_cont, quantile_disc",
        "in",
        "catalogue percentile 2 (H2O q6); p95 rollups (#326's comment)",
        True,
        sql="SELECT median(amount), quantile_cont(amount, 0.95), quantile_disc(amount, 0.5) FROM t",
    ),
    target(
        AREA,
        "arg_max, arg_min, max_by",
        "in",
        "catalogue arg_max 3; latest row per key",
        True,
        sql="SELECT arg_max(amount, ts), max_by(name, ts) FROM t GROUP BY qty",
    ),
    target(
        AREA,
        "string_agg, listagg, list, array_agg",
        "in",
        "catalogue string_agg 1; dbt.listagg; Ibis group_concat, collect verify",
        False,
        sql="SELECT string_agg(name, ',' ORDER BY id), list(name ORDER BY id) FROM t",
        issue=810,
    ),
    target(
        AREA,
        "bool_and, bool_or",
        "in",
        "dbt.bool_or; Ibis any, all verify",
        False,
        sql="SELECT bool_and(flag), bool_or(flag) FROM t",
        issue=810,
    ),
    target(
        AREA,
        "first and last with ORDER BY",
        "in",
        "catalogue first_last_value 2; Ibis first, last ordered",
        False,
        sql="SELECT first(name ORDER BY ts), last(name ORDER BY ts) FROM t",
        issue=810,
    ),
    target(
        AREA,
        "any_value",
        "in",
        "dbt.any_value; replay 56",
        False,
        sql="SELECT name, any_value(qty) FROM t GROUP BY name",
        issue=319,
    ),
    target(
        AREA,
        "approximate aggregates",
        "after",
        "catalogue approx_distinct; Ibis approx_nunique, approx_median",
        False,
        sql="SELECT approx_count_distinct(name) FROM t",
        ibis="approx_nunique",
        issue=469,
    ),
    target(
        AREA,
        "statistics as black boxes: mad, entropy, kurtosis, sem, product",
        "in",
        "metrics rollups; replay ~100",
        True,
        sql="SELECT mad(amount), entropy(name), kurtosis_pop(amount), sem(amount), "
        "product(amount) FROM t",
    ),
    target(
        AREA,
        "histogram and other MAP results",
        "after",
        "replay ~80",
        False,
        sql="SELECT histogram(qty) FROM t",
        issue=326,
        why="needs MAP in the model (#349)",
    ),
    target(
        AREA,
        "collect with NULLs kept",
        "after",
        "Ibis collect include_null",
        False,
        ibis="collect include_null",
        issue=505,
    ),
]

"""Spark runs lists (#94): `unnest`, a list literal, an element, the length and an unordered
`collect()`, with the rows the reference gives. An ordered `collect()` stays refused."""

from __future__ import annotations

import json
from typing import Any

import ibis
import pytest

from sverify._lean_eval import inline_tables, lean_values
from sverify.engine import written_plan
from sverify.ibis_substrait import to_substrait
from sverify.sql.core._base import Unsupported, to_sql
from sverify_spark.dialect import SPARK
from sverify_spark.engine import session

pytestmark = pytest.mark.backend("spark")

L = ibis.table({"k": "int64", "xs": "array<int64>"}, name="l")
T = ibis.table({"id": "int64", "name": "string", "qty": "int64"}, name="t")
L_ROWS = [(1, [1, 2, 3]), (2, []), (3, None), (4, [5, None]), (5, [7])]
T_ROWS = [(0, "a", 1), (1, "a", 2), (2, "b", None), (3, "b", 4), (4, None, 5)]

CASES: dict[str, Any] = {
    "unnest": (L.unnest("xs"), {"l": L_ROWS}),
    "list literal": (T.select("id", xs=ibis.literal([1, 2], "array<int64>")), {"t": T_ROWS}),
    "element and length": (L.select(L.k, a=L.xs[0], b=L.xs[-1], n=L.xs.length()), {"l": L_ROWS}),
    "collect": (T.group_by("name").aggregate(xs=T.qty.collect()), {"t": T_ROWS}),
    "collect then unnest": (
        T.group_by("name").aggregate(xs=T.qty.collect()).unnest("xs"),
        {"t": T_ROWS},
    ),
}


def bag(rows: list[tuple]) -> list[tuple]:
    """Rows as a multiset; the elements of a collected list in no order."""

    def f(v: Any) -> str:
        return repr(tuple(sorted(map(repr, v)))) if isinstance(v, (list, tuple)) else repr(v)

    return sorted(tuple(f(v) for v in r) for r in rows)


@pytest.mark.parametrize("label", CASES)
def test_spark_gives_the_references_rows(label: str) -> None:
    expr, tables = CASES[label]
    s = session()
    s.createDataFrame(L_ROWS, "k BIGINT, xs ARRAY<BIGINT>").createOrReplaceTempView("l")
    s.createDataFrame(T_ROWS, "id BIGINT, name STRING, qty BIGINT").createOrReplaceTempView("t")
    plan = written_plan(json.dumps(to_substrait(expr)))
    got = [tuple(r) for r in s.sql(to_sql(plan, SPARK)).collect()]
    want = lean_values(json.dumps(inline_tables(json.loads(plan), tables)))
    assert bag(got) == bag(want), label


def test_an_ordered_collect_is_refused() -> None:
    expr = T.group_by("name").aggregate(xs=T.qty.collect(order_by="qty"))
    with pytest.raises(Unsupported, match="array_agg|collect"):
        to_sql(written_plan(json.dumps(to_substrait(expr))), SPARK)

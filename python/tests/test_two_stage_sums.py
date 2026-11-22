"""The two-stage double `SUM` and `AVG` (ruling 212, #1608 item 7, #1787).

A grouped double `SUM` or `AVG` checks its value with aggregates of its own
(`SqlWriter.sum_checks`). In two stages the first computes the sums and counts,
and the second those checks only over the rows of the groups whose sum is not
finite. It rests on a finite sum having finite values: proved in Lean for the
summation orders with a shape (`SumOrder.isFinCode`,
`analysis/Sverify/Analysis/FiniteSum.lean`) and a probed engine fact for the
others (A2). The SQL rewrite is tested here against the one-stage form, not
proved (B1)."""

import json
import math
import re
import subprocess
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import fields
from pathlib import Path

import duckdb
import ibis
import pyarrow as pa
import pytest
from hypothesis import example, given, settings, target
from hypothesis import strategies as st

from _repo import ROOT, needs_repo
from sverify.engine import checker_path
from sverify.ibis_substrait import to_substrait_json
from sverify.sql import DIALECTS, dialect_of, to_sql
from sverify.sql.core._base import Dialect

#: The `sum_order` behaviours `SumOrder.isFinCode` proves the statement for.
LEMMA = Path("analysis/Sverify/Analysis/FiniteSum.lean")

#: The behaviours without a shape, each with the fact and probe that carry the
#: statement on its engine (ruling 212, A2).
PROBED = {
    ("duckdb", "SCALED_CONSTANT"): (
        "engines/duckdb/facts/duckdb-sum-double.json",
        "engines/duckdb/replay/probes.json",
        "sum-constant-run-nonfinite",
    ),
    ("polars", "COMPENSATED"): (
        "engines/polars/facts/polars-sum-float.json",
        "engines/polars/probes/probes.json",
        "float-sum-grouped-nonfinite",
    ),
}

INF = math.inf


def _proved() -> set[str]:
    text = (ROOT / LEMMA).read_text()
    m = re.search(r"\(hb : b ∈ \[([^\]]*)\]\)", text)
    assert m, "SumOrder.isFinCode's list of behaviours"
    return set(re.findall(r'"([A-Z_]+)"', m.group(1)))


@needs_repo
def test_every_sum_order_of_a_two_stage_engine_is_covered():
    """A3: an engine writes two stages only where each `sum_order` behaviour of
    its table is proved (`SumOrder.isFinCode`) or carried by a probed fact,
    and each such fact cites its probe, which is recorded."""
    out = subprocess.run(
        [str(checker_path()), "--options"], capture_output=True, text=True, check=True
    )
    choices = json.loads(out.stdout)["choices"]
    proved = _proved()
    assert {"ANY", "SEQUENTIAL"} <= proved
    for (engine, b), (fact, probes, construct) in PROBED.items():
        doc = json.loads((ROOT / fact).read_text())
        cited = [e for c in doc["provenance"] for e in c.get("evidence", [])]
        assert {"file": probes, "probe": construct} in cited, (engine, b)
        recorded = {p["construct"] for p in json.loads((ROOT / probes).read_text())["probes"]}
        assert construct in recorded, (engine, b)
    for engine in DIALECTS:
        try:
            on = dialect_of(engine).two_stage_sums
        except ValueError:  # an engine whose plugin is not installed
            continue
        if not on:
            continue
        rows = choices.get(engine, [])
        row = next(r for r in rows if r["option"] == "sum_order" and r["group"] is None)
        for b in row["choice"]["behaviours"]:
            assert b in proved or (engine, b) in PROBED, (engine, b)


# The differential (B2, B3): the two-stage SQL against the one-stage SQL, on
# DuckDB, the same rows or a refusal of the same kind.

T = ibis.table({"k": "int64", "s": "string", "x": "float64", "y": "float64"}, name="t")
U = ibis.table({"k": "int64", "w": "float64"}, name="u")

SHAPES = {
    "sum-avg": T.group_by("k").aggregate(a=T.x.sum(), b=T.x.mean(), n=T.x.count()),
    "two-keys": T.group_by(["k", "s"]).aggregate(a=T.x.sum()),
    "no-keys": T.aggregate(a=T.x.sum(), b=T.y.mean()),
    "two-measures": T.group_by("k").aggregate(a=T.x.sum(), b=T.y.sum(), c=T.y.max()),
    "filter": T.filter(T.y > 0).group_by("s").aggregate(a=T.x.mean()),
    "join": T.join(U, "k").group_by("k").aggregate(a=(T.x + U.w).sum()),
}

VALUES = st.sampled_from([0.0, 1.0, -2.5, 1e300, -1e300, 1e308, -1e308, INF, -INF, math.nan, None])
KEYS = st.sampled_from([0, 1, 2, None])
ROWS = st.lists(st.tuples(KEYS, st.sampled_from(["a", "b", None]), VALUES, VALUES), max_size=12)


@contextmanager
def _switch(on: bool) -> Iterator[None]:
    """DuckDB's dialect writing two stages or one."""
    cls = type(dialect_of("duckdb"))
    was = cls.two_stage_sums
    cls.two_stage_sums = on
    try:
        yield
    finally:
        cls.two_stage_sums = was


def _sql(q: ibis.Table, two: bool, **kw) -> str:
    with _switch(two):
        return to_sql(to_substrait_json(q), "duckdb", **kw)


#: Each shape's SQL, one stage and two.
WRITTEN = {name: (_sql(q, False), _sql(q, True)) for name, q in SHAPES.items()}


#: The errors a grouped double `SUM` or `AVG` raises.
RAISES = {"domain error", "overflow to infinity"}


def _run(sql: str, rows: list[tuple], extra: list[tuple]) -> object:
    con = duckdb.connect()
    k, s, x, y = zip(*rows, strict=True) if rows else ([], [], [], [])
    con.register("t", pa.table({
        "k": pa.array(k, pa.int64()), "s": pa.array(s, pa.string()),
        "x": pa.array(x, pa.float64()), "y": pa.array(y, pa.float64()),
    }))  # fmt: skip
    uk, uw = zip(*extra, strict=True) if extra else ([], [])
    con.register("u", pa.table({"k": pa.array(uk, pa.int64()), "w": pa.array(uw, pa.float64())}))
    try:
        out = con.execute(sql).fetchall()
    except duckdb.Error as e:
        kind = re.search(r"sverify: ([a-z ]+):", str(e))
        assert kind and kind.group(1) in RAISES, e
        # Which error a run reports is open: the reference says that the plan
        # raises, not which group's error comes first (`Issue` is a set).
        return "raised"
    # NaN is equal to itself here, and rows come in any order.
    return sorted(repr(r) for r in out)


def _nonfinite_groups(rows: list[tuple]) -> int:
    sums: dict = {}
    for k, _, x, _ in rows:
        if x is not None:
            sums[k] = sums.get(k, 0.0) + x
    return sum(not math.isfinite(v) for v in sums.values())


@pytest.mark.parametrize("shape", SHAPES)
@settings(deadline=None)
@given(rows=ROWS, extra=st.lists(st.tuples(KEYS, VALUES), max_size=4))
@example(rows=[(1, "a", INF, 1.0), (1, "a", -INF, 1.0), (2, "b", 1.0, 1.0)], extra=[(1, 1.0)])
@example(rows=[(1, "a", 1e308, 1.0), (1, "a", 1e308, 1.0), (2, "b", 1.0, 1.0)], extra=[(1, 0.0)])
@example(
    rows=[(1, "a", 1e308, 1e308), (1, "a", 1e308, 1e308), (1, "a", -1e308, -1e308)],
    extra=[(1, 0.0)],
)
@example(rows=[(None, None, INF, math.nan), (None, None, 1.0, 1.0)], extra=[(None, 1.0)])
@example(rows=[(1, "a", None, None), (2, "b", 1.0, 2.0)], extra=[(2, 1.0)])
@example(rows=[], extra=[])
def test_two_stages_give_what_one_stage_gives(shape, rows, extra):
    """B2: on every input, two stages give the one-stage form's rows, or both
    raise. Where groups fail differently (one overflows, one is a domain error)
    each plan may report either error: the reference leaves the order open."""
    target(_nonfinite_groups(rows), label="groups whose sum is not finite")
    one, two = WRITTEN[shape]
    assert "WITH" in two and "WITH" not in one  # B3: the two-stage form was written
    assert _run(two, rows, extra) == _run(one, rows, extra)


def test_a_constant_run_of_infinity_from_a_stored_table():
    """B2: DuckDB adds a constant-compressed run as one product (the
    `SCALED_CONSTANT` order); its sum is not finite, so the second stage
    checks the group, as one stage does."""
    q = ibis.table({"k": "int64", "x": "float64"}, name="t")
    plan = to_substrait_json(q.group_by("k").aggregate(a=q.x.sum()))
    con = duckdb.connect()
    con.execute("ATTACH ':memory:' AS m (COMPRESS)")
    con.execute(
        "CREATE TABLE m.t AS SELECT 1 AS k, 'inf'::DOUBLE AS x FROM range(130000)"
        " UNION ALL SELECT 2, '-inf'::DOUBLE FROM range(130000)"
        " UNION ALL SELECT 2, 'inf'::DOUBLE FROM range(130000) ORDER BY k"
    )
    con.execute("CHECKPOINT m")
    con.execute("USE m")
    found = []
    for two in (False, True):
        with _switch(two), pytest.raises(duckdb.Error, match="sverify: domain error") as e:
            con.execute(to_sql(plan, "duckdb")).fetchall()
        found.append(str(e.value).split(":")[1])
    assert found[0] == found[1]


def _two(q: ibis.Table, **kw) -> bool:
    return "WITH " in _sql(q, True, **kw)


def test_where_two_stages_apply():
    """C2-C4: keys that compare NULL-safely as the engine groups them, an input
    read twice as the same rows, and a measure whose checks one stage writes."""
    f = ibis.table({"d": "float64", "x": "float64", "k": "int64"}, name="f")
    assert _two(f.group_by("k").aggregate(a=f.x.sum()))
    # A double key (C3), an input whose rows are a choice (C2), no double sum.
    assert not _two(f.group_by("d").aggregate(a=f.x.sum()))
    assert not _two(f.limit(5).group_by("k").aggregate(a=f.x.sum()))
    assert not _two(f.group_by("k").aggregate(a=f.x.max()))
    # C4: no checks, no second stage; a lens keeps the aggregates' checks.
    assert not _two(f.group_by("k").aggregate(a=f.x.sum()), guards=False, finite=False)
    assert _two(f.group_by("k").aggregate(a=f.x.sum()), guards=False, finite="aggregates")


def test_the_switch_is_internal():
    """C5: a class attribute, outside `Dialect`'s public fields."""
    assert "two_stage_sums" not in {f.name for f in fields(Dialect)}

"""The replay of Polars's own unit tests (#2615, `sverify_dev.polars_tests`):
its translator and comparison on plans of its own, and the ledgers it writes.

The replay itself needs Polars's test sources at the pinned tag, which it
fetches; the ledger tests read what it wrote."""

from __future__ import annotations

import json
import re
import warnings

import polars as pl
import pytest

from _repo import needs_repo
from sverify_dev import polars_tests as replay

pytestmark = pytest.mark.backend("polars")

FRAME = pl.LazyFrame(
    {"a": [1, 2, None, -7], "b": ["x", "y", "x", "y"], "f": [1.0, None, 2.5, float("nan")]}
)


def _plan(lf: pl.LazyFrame) -> str:
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        return lf.serialize(format="json")


@pytest.mark.parametrize(
    "lf",
    [
        FRAME.filter(pl.col("a") > 1),
        FRAME.group_by("b").agg(pl.col("a").sum().alias("s"), (pl.col("a") % 2).max(), pl.len()),
        FRAME.with_columns(
            pl.when(pl.col("a").is_null()).then(0).otherwise(pl.col("a")).alias("d")
        ),
        FRAME.sort("a", nulls_last=True).select("a", "b"),
        FRAME.join(FRAME.select("b", z=pl.col("a")), on="b", how="left"),
        FRAME.select(pl.col("a").sum().over("b")),
        FRAME.select(pl.col("a") // 2, pl.col("a").fill_null(0).alias("z")),
        FRAME.select(pl.col("a").sum(), pl.col("a").max().alias("m")),
        FRAME.select((pl.col("a") == pl.lit(None)).alias("eq")),
    ],
    ids=["filter", "group_by", "when", "sort", "join", "over", "floordiv", "aggregate", "eq_null"],
)
def test_the_model_the_engine_and_polars_agree(lf: pl.LazyFrame) -> None:
    assert replay.replay_collect(_plan(lf), lf.collect()) == {"outcome": "agree"}


def test_another_result_than_polarss_is_found() -> None:
    """The comparison is not vacuous: rows Polars did not give, or its rows in
    another order under a sort, leave the collect unattributed."""
    lf = FRAME.filter(pl.col("a") > 1)
    other = FRAME.filter(pl.col("a") > 0).collect()
    assert replay.replay_collect(_plan(lf), other)["outcome"] == "unattributed"
    lf = FRAME.sort("a", descending=True, nulls_last=True)
    other = FRAME.sort("a", nulls_last=True).collect()
    assert replay.replay_collect(_plan(lf), other)["outcome"] == "unattributed"


def test_rows_that_tie_may_come_in_any_order() -> None:
    """Under a sort the keys are in order and the rows that tie on them may
    come in any order the model allows: Polars's own order of ties agrees."""
    lf = FRAME.sort("b", nulls_last=True)
    got = lf.collect()
    swapped = pl.concat([got[1:2], got[0:1], got[2:]])  # the two `x` rows tie
    assert swapped["b"].to_list()[:2] == ["x", "x"]
    assert replay.replay_collect(_plan(lf), swapped) == {"outcome": "agree"}


def test_a_literal_the_json_plan_loses_is_not_read() -> None:
    """Polars's JSON writes a NaN or an infinite literal as `null`, which is no
    NULL: the translator skips it."""
    lf = FRAME.select(pl.col("f") < float("inf"))
    out = replay.replay_collect(_plan(lf), lf.collect())
    assert out["outcome"] == "skipped" and "non-finite" in out["reason"]


def test_the_translator_names_what_it_does_not_read() -> None:
    lf = FRAME.with_row_index()
    out = replay.replay_collect(_plan(lf), lf.collect())
    assert out == {"outcome": "skipped", "reason": "translator: MapFunction RowIndex"}


def test_a_tests_outcome_is_its_worst_collects() -> None:
    rec = {
        "test": "tests/unit/x.py::t",
        "passed": True,
        "skip": None,
        "replays": [{"outcome": "agree"}, {"outcome": "refused", "construct": "c"}],
    }
    assert replay.classify(rec, {})["outcome"] == "refused"
    unattributed = {"outcome": "unattributed", "reason": "r", "plan": "p"}
    rec["replays"].append(unattributed)
    assert replay.classify(rec, {})["outcome"] == "unattributed"
    triaged = {"tests/unit/x.py::t@p": {"as": "skipped: translation", "reason": "why"}}
    assert replay.classify(rec, triaged)["outcome"] == "refused"


@needs_repo
def test_polars_is_the_release_the_lock_pins() -> None:
    lock = (replay.ROOT / "python" / "uv.lock").read_text()
    m = re.search(r'name = "polars"\nversion = "([^"]+)"', lock)
    assert m and f"py-{m[1]}" == replay.TAG


@needs_repo
def test_the_ledgers_count_their_results_and_name_their_source() -> None:
    ledgers = [p for p in sorted(replay.LEDGERS.glob("*.json")) if p != replay.TRIAGE]
    assert ledgers
    for p in ledgers:
        led = json.loads(p.read_text())
        assert led["module"] == p.stem and led["polars"] == replay.TAG
        assert led["license"] == "MIT"
        counts = dict.fromkeys(replay.OUTCOMES, 0)
        for r in led["results"].values():
            counts[r["outcome"]] += 1
        assert led["summary"] == counts
    assert (replay.LEDGERS / "LICENSE-polars").read_text().startswith("Copyright")


@needs_repo
def test_no_disagreement_and_no_untriaged_collect_is_stored() -> None:
    """A disagreement is a model or lowering finding: fixed, or recorded in
    triage with its issue. An unattributed collect is triaged (P3)."""
    for p in sorted(replay.LEDGERS.glob("*.json")):
        if p == replay.TRIAGE:
            continue
        for test, r in json.loads(p.read_text())["results"].items():
            assert r["outcome"] != "disagree" or r.get("issue"), f"{p.stem}::{test}"
            assert r["outcome"] != "unattributed" or "triaged" in r, f"{p.stem}::{test}"

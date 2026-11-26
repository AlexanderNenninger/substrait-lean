"""A sink records the engine, the engine's version, the release of sverify and the
profile that wrote a state, and a resume says what differs (#1485, ruling 96)."""

import json
from dataclasses import replace
from pathlib import Path
from typing import Any

import pyarrow as pa
import pytest

import sverify as sv
from sverify import incremental, profiles
from sverify.incremental import Pipeline, Stored, plan_digest
from sverify.io import Changes, Contract, StaticSource

TABLE = pa.table({"k": [1, 2], "x": [0.0, 1.5]})


@sv.transform()
def positive(t):
    return t.filter(t.k > 0)


@sv.transform(semantics="duckdb")
def positive_as_duckdb(t):
    return t.filter(t.k > 0)


def view(engine: str, query, *, resume: Stored | None = None):
    con = sv.connect(engine)
    pipe = Pipeline(con, engine)
    t = pipe.source("t", StaticSource(TABLE, name="t"))
    return pipe.view("v", query(t), resume=resume)


def stored_by(v, **fields: Any) -> Stored:
    """What a sink that held `v`'s state under `fields` stored."""
    now = profiles.runtime(v.engine)
    base: dict[str, Any] = {f: now[f] for f in profiles.RUNTIME_FIELDS}
    base["semantics"] = v.profile
    stored = Stored(
        "x@v1",
        "x",
        plan_digest(v.plan, profile=v.profile),
        dict(v.pipeline.lineage("t")),
        v.pipeline.digests("t"),
        v.table.to_pyarrow(),
    )
    return replace(stored, **{**base, **fields})


def under_duckdb(query, **fields: Any) -> Stored:
    return stored_by(view("duckdb", query), **{"engine": "duckdb", **fields})


def test_the_runtime_names_the_engine_its_library_and_the_release() -> None:
    now = profiles.runtime("duckdb")
    assert now["engine"] == "duckdb"
    assert now["engine_version"] and now["sverify"] == sv.__version__


def test_a_deterministic_view_resumes_on_another_engine_and_says_so() -> None:
    stored = under_duckdb(lambda t: positive(t), engine_version="0.0.1")
    v = view("polars", lambda t: positive(t), resume=stored)
    assert v.resumed is not None and v.resumed.startswith("resumed from x@v1")
    assert "the engine changed: engine duckdb → polars" in v.resumed
    assert set(v.record_changes) >= {"engine", "engine_version"}
    assert v.record_changes["engine"] == ("duckdb", "polars")


def test_a_view_with_an_open_value_is_recomputed_once_on_another_engine() -> None:
    # Uncontracted: no report says the plan is determined, so a delta could retract
    # a row the other engine did not compute.
    stored = under_duckdb(lambda t: t.filter(t.k > 0))
    v = view("polars", lambda t: t.filter(t.k > 0), resume=stored)
    assert v.resumed is not None and v.resumed.startswith("computed: the engine changed (")
    assert "the plan leaves a value open" in v.resumed


def test_a_view_that_is_recomputed_and_diffed_resumes_on_another_engine() -> None:
    def ranked(t):
        return t.mutate(r=t.k.rank())

    stored = under_duckdb(ranked)
    v = view("polars", ranked, resume=stored)
    assert v.fallback is not None and v.touched is None
    assert v.resumed is not None and v.resumed.startswith("resumed from")
    assert "the engine changed: engine duckdb → polars" in v.resumed


def test_a_record_without_the_fields_resumes_with_no_line() -> None:
    bare = dict.fromkeys(profiles.RUNTIME_FIELDS)
    stored = under_duckdb(lambda t: positive(t), **bare, semantics=None)
    v = view("polars", lambda t: positive(t), resume=stored)
    assert v.resumed == "resumed from x@v1"
    assert v.record_changes == {}


def test_another_release_alone_is_in_the_structured_result_only() -> None:
    stored = under_duckdb(lambda t: positive(t), sverify="0.0.1")
    v = view("duckdb", lambda t: positive(t), resume=stored)
    assert v.resumed == "resumed from x@v1"
    assert v.record_changes == {"sverify": ("0.0.1", sv.__version__)}


def test_the_same_plan_under_two_profiles_is_recomputed_and_names_both() -> None:
    stored = under_duckdb(lambda t: positive(t))
    assert stored.semantics == "portable"
    v = view("duckdb", lambda t: positive_as_duckdb(t), resume=stored)
    assert v.profile == "duckdb"
    assert v.resumed is not None and v.resumed.startswith("computed:")
    assert "semantics='portable'" in v.resumed and "semantics='duckdb'" in v.resumed


def test_the_profile_is_a_component_of_the_digest_unless_it_is_the_reference() -> None:
    plan = view("duckdb", lambda t: positive(t)).plan
    assert plan_digest(plan, profile="portable") == plan_digest(plan)
    assert plan_digest(plan, profile="duckdb") != plan_digest(plan)
    assert plan_digest(plan, profile="duckdb") != plan_digest(plan, profile="polars")


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_retraction_of_minus_zero_cancels_a_state_row_of_zero(engine: str) -> None:
    con = sv.connect(engine)
    pipe = Pipeline(con, engine)
    src = StaticSource(TABLE, name="t")
    t = pipe.source("t", src)
    v = pipe.view("v", t.filter(t.k > 0))
    pipe.refresh()
    src.apply(Changes(deletes=pa.table({"k": [1], "x": [-0.0]})))
    pipe.refresh(audit=True)
    assert [tuple(r.values()) for r in v.table.to_pyarrow().to_pylist()] == [(2, 1.5)]


def test_a_contract_with_the_fields_is_in_the_schema_and_an_old_one_still_reads() -> None:
    jsonschema = pytest.importorskip("jsonschema")
    schema = json.loads(
        (Path(sv.__file__).parent / "schemas" / "sink-contract.schema.json").read_text()
    )
    v = view("duckdb", lambda t: positive(t))
    c = Contract(
        node="v",
        plan=plan_digest(v.plan),
        sources={},
        epoch=0,
        not_null=[],
        checks={},
        unique=[],
        **dict[str, Any](profiles.runtime("duckdb"), semantics="portable"),
    )
    record = json.loads(c.to_json())
    jsonschema.validate(record, schema)
    assert record["engine"] == "duckdb" and record["sverify"] == sv.__version__
    old = {k: v for k, v in record.items() if k not in {*profiles.RUNTIME_FIELDS, "semantics"}}
    jsonschema.validate(old, schema)
    read = Contract.from_json(json.dumps(old))
    assert read.engine is None and read.semantics is None
    assert incremental.plan_digest(v.plan) == read.plan

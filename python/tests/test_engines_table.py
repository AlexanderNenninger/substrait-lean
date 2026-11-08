"""The engines sverify names come from one table (`sverify._engines`), and
the types that name the profiles agree with the checker's (`--options`,
`"profiles"`, #1166)."""

from __future__ import annotations

from typing import get_args

from sverify import _engines, engines
from sverify.engine import _LOCAL_ENGINES, Engine
from sverify.report import Semantics
from sverify.routes import _options_json
from sverify.sql import DIALECTS


def _checker_profiles() -> dict[str, dict]:
    return _options_json()["profiles"]


def test_semantics_are_the_checker_s_profiles() -> None:
    """A plan is verified under any profile of the checker but the core."""
    assert set(get_args(Semantics)) == set(_checker_profiles()) - {"core"}


def test_engines_are_the_checker_s_engine_profiles() -> None:
    """`Engine` names the checker's engine profiles."""
    named = {e for e, p in _checker_profiles().items() if p.get("engine")}
    assert set(get_args(Engine)) == named


def test_every_engine_has_a_row() -> None:
    assert set(get_args(Engine)) <= _engines.NAMED
    assert set(engines.ENGINES) <= set(get_args(Engine))
    assert set(_LOCAL_ENGINES) == {*engines.ENGINES, "datafusion"}
    assert set(DIALECTS) <= _engines.NAMED


def test_every_engine_a_plan_runs_on_has_a_translation() -> None:
    assert {*get_args(Engine), *_LOCAL_ENGINES} <= set(_engines.TRANSLATIONS)

"""The engines sverify names, in one table (#1166).

Internal: not part of sverify's public API. One row per engine says where it
runs: a `Connection` runs a plan on it, or a `to_sql` dialect writes it, or
both; the modules it needs; and the translation from the reference that makes
a run on it sound. The sets the rest of sverify reads are derived from it.
Which engines have a profile of their own is the checker's (`substrait-check
--options`, `"profiles"`); `tests/test_engines_table.py` checks the types that
name them (`Engine`, `Semantics`) against it.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import NamedTuple


class EngineRow(NamedTuple):
    """Where an engine runs and what makes a run on it sound."""

    name: str
    #: A `Connection` runs plans on it (`sverify.engines.run`).
    local: bool
    #: Outside the 1.x promise: a `Connection` runs it, `ENGINES` leaves it
    #: out (`docs/stability.md`).
    optional: bool
    #: `to_sql` writes its dialect.
    dialect: bool
    #: The modules a run on it needs (`sverify.testing.installed_engines`).
    modules: tuple[str, ...]
    #: The translation from the reference to it, with what makes it sound.
    translation: str | None


TABLE: tuple[EngineRow, ...] = (
    EngineRow(
        "duckdb",
        local=True,
        optional=False,
        dialect=True,
        modules=(),
        translation="sverify's DuckDB lowering, proved for every plan, and its SQL writer",
    ),
    EngineRow(
        "polars",
        local=True,
        optional=False,
        dialect=False,
        modules=("polars", "numpy"),
        translation="sverify's Polars translation, with shims where Polars differs from the "
        "reference, tested against the reference",
    ),
    EngineRow(
        "datafusion",
        local=True,
        optional=True,
        dialect=False,
        modules=("datafusion",),
        translation="sverify's SQL writer, with shims where DataFusion differs from the "
        "reference, tested against the reference",
    ),
    EngineRow(
        "spark",
        local=False,
        optional=False,
        dialect=True,
        modules=("pyspark",),
        translation="sverify's Spark SQL writer, with shims where Spark differs from the "
        "reference, proved against Spark's facts (Rel.spark_sound) and tested against "
        "the reference",
    ),
    EngineRow(
        "snowflake",
        local=False,
        optional=False,
        dialect=True,
        modules=(),
        translation=None,
    ),
)

#: The engines a `Connection` runs plans on within the 1.x promise
#: (`sverify.engines.ENGINES`).
LOCAL: tuple[str, ...] = tuple(r.name for r in TABLE if r.local and not r.optional)
#: The engines a `Connection` accepts: `LOCAL` and the optional ones.
ACCEPTED: tuple[str, ...] = tuple(r.name for r in TABLE if r.local)
#: The dialects `to_sql` writes.
DIALECTS: tuple[str, ...] = tuple(r.name for r in TABLE if r.dialect)
#: Every engine sverify names: a row of `_support.SUPPORT` names only these.
NAMED: frozenset[str] = frozenset(r.name for r in TABLE)
#: The modules each engine needs.
MODULES: Mapping[str, tuple[str, ...]] = {r.name: r.modules for r in TABLE}
#: The translation to each engine that has one of sverify's own.
TRANSLATIONS: Mapping[str, str] = {r.name: r.translation for r in TABLE if r.translation}


def translations() -> dict[str, str]:
    """`TRANSLATIONS`, with those of the installed profiles from outside
    sverify (`sverify.profiles`)."""
    from sverify import profiles as plugged

    return {**TRANSLATIONS, **{e: p.translation for e, p in plugged.plugins().items()}}

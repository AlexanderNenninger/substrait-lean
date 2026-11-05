"""Hooks between sverify's core and the `sverify` command (#744).

Internal: not part of sverify's public API. The module imports nothing of
sverify at load time, so the core can move without moving these.

* `collecting`: within the block, contracted transforms record their proofs,
  one `Collected` per call, instead of raising `VerificationError` or
  `CompositionError`, and `refresh` raises. `sverify.cli.discover` imports a
  pipeline's file this way.
* `planned`: within the block, `Group.refresh` calls the callback once the
  routes are chosen, before any data moves; the CLI ends the time budget
  there.
* `set_memory_limit`: DuckDB's `memory_limit` for the process's database,
  with a directory to spill to (#783).
"""

from __future__ import annotations

import os
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from sverify.contracts import CompositionError, ContractedTransform, Report


@dataclass
class Collected:
    """One call of a contracted transform while `collecting`: what it was
    applied to and the report of its proof, recorded instead of raised."""

    transform: ContractedTransform
    """The transform called."""
    node: bool
    """Whether the call built a `sverify.Node` (on sources or nodes)."""
    report: Report | None = None
    """The report of the postconditions' proof; None while it runs (or if
    it never finished)."""
    links: list[CompositionError] = field(default_factory=list)
    """Preconditions on another transform's result that its guarantees do
    not imply."""
    params: dict[str, str] = field(default_factory=dict)
    """For each input table the report names, the transform's parameter
    that reads it (`requires` is keyed by parameter)."""


COLLECTING: ContextVar[list[Collected] | None] = ContextVar("sverify_collecting", default=None)
PLANNED: ContextVar[Callable[[], None] | None] = ContextVar("sverify_planned", default=None)


@contextmanager
def collecting() -> Iterator[list[Collected]]:
    """Record the proofs of contracted transforms in the list it yields."""
    out: list[Collected] = []
    token = COLLECTING.set(out)
    try:
        yield out
    finally:
        COLLECTING.reset(token)


def is_collecting() -> bool:
    """Whether a `collecting` block is open."""
    return COLLECTING.get() is not None


@contextmanager
def planned(callback: Callable[[], None]) -> Iterator[None]:
    """Have `Group.refresh` call `callback` once its routes are chosen."""
    token = PLANNED.set(callback)
    try:
        yield
    finally:
        PLANNED.reset(token)


def set_memory_limit(limit: str) -> None:
    """Give the process's DuckDB database `memory_limit` `limit` (`"2GB"`)
    and a spill directory, now and whenever it opens again."""
    from sverify import _duckdb

    os.environ["SVERIFY_MEMORY_LIMIT"] = limit
    _duckdb.apply_limits()

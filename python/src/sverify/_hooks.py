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

And between the layers of the core (#730, `docs/layers.md`), where a lower
one needs a higher one: the higher module registers itself when it loads.
`import sverify` loads its public names on first use, so the first call of a
hook loads its module by name.

* `nodes` (`NodeHooks`, from `sverify.nodes`): a source's `pipe` and a
  transform called on sources build nodes.
* `export` (`sverify.substrait_export`) and `report_json`: a `Report`
  written and read as Substrait and as JSON.
* `lineage` (`sverify.openlineage`): a refresh's OpenLineage events.

`nodes` is registered by its module; the others load their module by name.
"""

from __future__ import annotations

import importlib
import os
from collections.abc import Callable, Iterator, Mapping, Sequence
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from sverify.contracts import CompositionError, ContractedTransform, Report
    from sverify.nodes import Node


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


@dataclass(frozen=True)
class NodeHooks:
    """What `sverify.nodes` lends the layers below it."""

    is_node: Callable[[Any], bool]
    """A node or a source (`sverify.io`) rather than an Ibis table."""
    source_node: Callable[[Any], Node]
    """The node of a source, one per source."""
    derive: Callable[[ContractedTransform, Sequence[Any], dict[str, Any]], Node]
    """A transform applied to sources and nodes, as a node."""


_HOOKS: list[NodeHooks] = []


def register_nodes(hooks: NodeHooks) -> None:
    """Called by `sverify.nodes` when it loads."""
    _HOOKS[:] = [hooks]


def nodes() -> NodeHooks:
    """The hooks `sverify.nodes` registered."""
    if not _HOOKS:
        importlib.import_module("sverify.nodes")
    return _HOOKS[0]


def wants_node(args: Sequence[Any], kwargs: Mapping[str, Any]) -> bool:
    """A transform called on these arguments builds a node."""
    is_node = nodes().is_node
    return any(is_node(v) for v in [*args, *kwargs.values()])


def export() -> Any:
    """`sverify.substrait_export`, which writes and reads a report as
    Substrait."""
    return importlib.import_module("sverify.substrait_export")


def report_json() -> Any:
    """`sverify.report_json`, which writes and reads a report as JSON."""
    return importlib.import_module("sverify.report_json")


def lineage() -> Any:
    """`sverify.openlineage`, which sends a refresh's OpenLineage events."""
    return importlib.import_module("sverify.openlineage")

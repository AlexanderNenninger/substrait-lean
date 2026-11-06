"""Piping, below the layers that build nodes: `Pipeable`, the `pipe` of
sources, and `bind`, how a step takes its inputs (#730).

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

It sits below the sources (`sverify.incremental`, `sverify.io`), which
inherit `Pipeable`; `pipe` builds its node through `sverify._hooks.nodes`.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from typing import TYPE_CHECKING, Any, Literal

from sverify import _hooks

if TYPE_CHECKING:
    import ibis.expr.types as ir

    from sverify.contracts import ContractedTransform
    from sverify.nodes import Node


type Step = Callable[..., ir.Table] | ContractedTransform
"""What `pipe` takes: a contracted transform, a SQL step or a plain function
from Ibis tables to an Ibis table."""


class Pipeable:
    """`pipe` for the sources of `sverify.io`: `orders.pipe(paid)` is the
    node `paid` builds over the source, as `paid(orders)`."""

    on_violation: Literal["error", "quarantine", "hold"] | None = None
    """What a refresh does with a batch that breaks a precondition on this
    source, unless the transform stating it sets its own (#184)."""

    def pipe(self, step: Step, /, **inputs: Any) -> Node:
        """Apply `step` to this source: see `sverify.Node.pipe`.

        Args:
            step: A contracted transform, a SQL step (`sverify.sql(query)`)
                or a plain function from Ibis tables to an Ibis table.
            **inputs: The step's other inputs, by parameter name (for a SQL
                step, by the table names the query reads).

        Returns:
            The node `step` builds, with its contract checked.
        """
        return _hooks.nodes().source_node(self).pipe(step, **inputs)


def bind(
    step: ContractedTransform, chained: Any, inputs: Mapping[str, Any]
) -> tuple[tuple[Any, ...], dict[str, Any]]:
    """The chained node in the step's first parameter, the other inputs by
    keyword; a missing, duplicate or unknown input raises `TypeError`, which
    names the step's parameters."""
    params = [
        p
        for p in step.signature.parameters.values()
        if p.kind in (p.POSITIONAL_ONLY, p.POSITIONAL_OR_KEYWORD)
    ]
    names = ", ".join(step.signature.parameters)
    if not params:
        raise TypeError(f"{step.name}({names}) has no parameter for the chained node")
    first = params[0].name
    if first in inputs:
        raise TypeError(
            f"{step.name}({names}): {first!r} is given twice, as the chained node "
            "(its first parameter) and by keyword"
        )
    try:
        bound = step.signature.bind(chained, **inputs)
    except TypeError as e:
        raise TypeError(
            f"{step.name}({names}) takes the chained node as {first!r} and the rest by keyword: {e}"
        ) from None
    return bound.args, bound.kwargs

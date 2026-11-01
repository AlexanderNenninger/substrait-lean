"""Steps: what `Node.pipe` takes, and `pipe` on sources.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

    orders.pipe(paid).pipe(enrich, customers=customers)

A step is a contracted transform (`sverify.transform`), a SQL step
(`sverify.sql(query)`) or a plain function from Ibis tables to an Ibis
table, which is lifted to a transform with no contract. The chained node
fills the step's first table parameter, and the other inputs come by
keyword. This module imports nothing heavy, so that sources
(`sverify.incremental`, `sverify.io`) can inherit `Pipeable`.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from typing import TYPE_CHECKING, Any

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
        from sverify.nodes import _source_node

        return _source_node(self).pipe(step, **inputs)  # type: ignore[arg-type]


def as_transform(step: Any) -> ContractedTransform:
    """`step` as a contracted transform: as it is, or a plain function lifted
    to a transform with no contract (`@sv.transform()`)."""
    from sverify.contracts import ContractedTransform, transform
    from sverify.nodes import Node, is_source

    if isinstance(step, ContractedTransform):
        return step
    if isinstance(step, Node) or is_source(step) or not callable(step):
        raise TypeError(
            f"pipe takes a step: a transform (@sv.transform), sv.sql(query) or a "
            f"function from Ibis tables to an Ibis table, got {step!r}"
        )
    lifted = transform()(step)
    if not lifted.name.isidentifier():  # a lambda
        lifted.name = "step"
    return lifted


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

"""Steps: what `Node.pipe` takes, and `pipe` on sources.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

    orders.pipe(paid).pipe(enrich, customers=customers)

A step is a contracted transform (`sverify.transform`), a SQL step
(`sverify.sql(query)`) or a plain function from Ibis tables to an Ibis
table, which is lifted to a transform with no contract. The chained node
fills the step's first table parameter, and the other inputs come by
keyword. `Pipeable`, `Step` and `bind` live in `sverify._pipe`, below the
sources that inherit `Pipeable` (#730).
"""

from __future__ import annotations

from typing import Any

from sverify._hooks import nodes
from sverify._pipe import Pipeable, Step, bind  # noqa: F401  (re-exported)
from sverify.contracts import ContractedTransform, transform


def as_transform(step: Any) -> ContractedTransform:
    """`step` as a contracted transform: as it is, or a plain function lifted
    to a transform with no contract (`@sv.transform(on_inferred="warn")`):
    it has no `requires` to state an inferred precondition in, so one is
    assumed, checked on the data, and named in a warning."""
    if isinstance(step, ContractedTransform):
        return step
    if nodes().is_node(step) or not callable(step):
        raise TypeError(
            f"pipe takes a step: a transform (@sv.transform), sv.sql(query) or a "
            f"function from Ibis tables to an Ibis table, got {step!r}"
        )
    lifted = transform(on_inferred="warn")(step)
    if not lifted.name.isidentifier():  # a lambda
        lifted.name = "step"
    return lifted

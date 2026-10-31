"""The exceptions sverify raises.

* `VerificationError`: Lean could not prove a postcondition; `.report` says
  what it could establish. `CompositionError` is the case where one
  transform's precondition does not follow from what the transform feeding
  it guarantees.
* `PreconditionError`, `PostconditionError`: a condition checked on the data
  failed (an input, or an output in `on_unproved="runtime"` mode).
* `NotIncremental`: a plan has no verified delta rules.
* `SchemaError`: a source's schema changed in a way a contract proved
  against the old schema cannot follow.
* `AuditError`: in `refresh(audit=True)`, a change feed or a view disagrees
  with recomputation; nothing was applied.
* `SqlError`: a SQL producer refused a query.
"""

from sverify.contracts import (
    CompositionError,
    PostconditionError,
    PreconditionError,
    VerificationError,
)
from sverify.engine import SqlError
from sverify.incremental import AuditError, NotIncremental, SchemaError

__all__ = [
    "AuditError",
    "CompositionError",
    "NotIncremental",
    "PostconditionError",
    "PreconditionError",
    "SchemaError",
    "SqlError",
    "VerificationError",
]

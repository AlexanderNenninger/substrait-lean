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
* `CheckerVersionError`: the `substrait-check` binary is older or newer than
  this sverify.
* `ConcurrentWriteError`: another process committed to a sink while this
  refresh wrote it; the write was not committed, and the next refresh
  recovers.
* `RouteError`: the plan is not proved, or no route takes it to an engine
  (`Report.run`, `Node.refresh`, #444); `.route` says why.
* `UnverifiedRunWarning`: a plan that is not proved runs, with
  `unverified=True`.
* `EngineVersionError`, `EngineVersionWarning`: an engine's version is not
  one its profile's facts were probed at (another major version refuses).
* `EngineSettingsError`, `EngineSettingsWarning`: an engine setting differs
  from the one its profile's facts were probed under.
* `Unsupported`: sverify refuses the input; the SQL lift, the Ibis producer,
  the checker, the SQL writer and the Polars translator all raise it (or a
  subclass), saying which construct. A `ValueError`; also
  `sverify.engines.Unsupported`.
* `ExportError`: a plan has no conforming Substrait form that keeps its
  proof (`Report.to_substrait`, #664); the message names the reason and the
  spec gap.
"""

from sverify._unsupported import Unsupported
from sverify.contracts import (
    CompositionError,
    PostconditionError,
    PreconditionError,
    VerificationError,
)
from sverify.engine import CheckerVersionError, SqlError
from sverify.incremental import AuditError, NotIncremental, SchemaError
from sverify.io._common import ConcurrentWriteError
from sverify.routes import (
    EngineSettingsError,
    EngineSettingsWarning,
    EngineVersionError,
    EngineVersionWarning,
    RouteError,
    UnverifiedRunWarning,
)
from sverify.substrait_export import ExportError

__all__ = [
    "AuditError",
    "CheckerVersionError",
    "CompositionError",
    "ConcurrentWriteError",
    "EngineSettingsError",
    "EngineSettingsWarning",
    "EngineVersionError",
    "EngineVersionWarning",
    "ExportError",
    "NotIncremental",
    "PostconditionError",
    "PreconditionError",
    "RouteError",
    "SchemaError",
    "SqlError",
    "Unsupported",
    "UnverifiedRunWarning",
    "VerificationError",
]

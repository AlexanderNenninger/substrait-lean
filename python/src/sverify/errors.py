"""The exceptions sverify raises.

Every exception below derives from `SverifyError`, so
`except sverify.errors.SverifyError` catches whatever sverify raises on
purpose; each also keeps its built-in base (`ValueError`, `RuntimeError`).
The same classes are importable where they are defined (`sverify.routes.RouteError`,
`sverify.engines.Unsupported`); import them from here.

* `VerificationError`: the checker could not prove a postcondition; `.report` says
  what it could establish. `CompositionError` is the case where one
  transform's precondition does not follow from what the transform feeding
  it guarantees.
* `PreconditionError`, `PostconditionError`: a condition checked on the data
  failed (an input, or an output in `on_unproved="check"` mode). A
  `PreconditionError` names the table (`.source`) and the condition
  (`.condition`), and holds up to ten of the rows that break it (`.rows`).
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
* `RouteError`: no route takes a plan to an engine (`Report.run`,
  `Node.refresh`, #444); `.route` says why.
* `UnverifiedRunError`: a run or refresh of a plan that is not proved,
  refused. It is a `VerificationError` and a `RouteError`.
* `UnverifiedRunWarning`: a plan that is not proved runs, with
  `unverified=True` or `transform(on_unproved="warn")`.
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

from sverify._unsupported import SverifyError, Unsupported
from sverify.contracts import (
    CompositionError,
    PostconditionError,
    PreconditionError,
    UnverifiedRunError,
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
    "SverifyError",
    "Unsupported",
    "UnverifiedRunError",
    "UnverifiedRunWarning",
    "VerificationError",
]

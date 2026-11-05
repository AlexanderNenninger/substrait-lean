"""The exceptions and warnings sverify raises.

Every exception below derives from `SverifyError`, so
`except sverify.errors.SverifyError` catches whatever sverify raises on
purpose; each also keeps its built-in base (`ValueError`, `RuntimeError`).
Each has a `code`, a snake_case string that names what failed and stays the
same across 1.x. Every warning derives from `SverifyWarning`. The same
classes are importable where they are defined (`sverify.routes.RouteError`,
`sverify.engines.UnsupportedError`); import them from here.

The proof:

* `VerificationError` (`not_proved`): the checker could not prove a
  postcondition; `.report` says what it could establish.
* `CompositionError` (`composition_not_proved`): one transform's
  precondition does not follow from what the transform feeding it
  guarantees. A `VerificationError`.
* `UnverifiedRunError` (`unverified_run`): a run or refresh of a plan that
  is not proved, refused. It is a `VerificationError` and a `RouteError`.

The data:

* `PreconditionError` (`precondition_failed`), `PostconditionError`
  (`postcondition_failed`): a condition checked on the data failed (an
  input, or an output in `on_unproved="runtime"` mode). A
  `PreconditionError` names the table (`.source`) and the condition
  (`.condition`), and holds up to ten of the rows that break it (`.rows`).
* `SchemaError` (`schema_changed`): a source's schema changed in a way a
  contract proved against the old schema cannot follow.
* `AuditError` (`audit_failed`): in `refresh(audit=True)`, a change feed or
  a view disagrees with recomputation; nothing was applied.

Running:

* `RouteError` (`route_refused`): no route takes a plan to an engine
  (`Report.run`, `Node.refresh`, #444); `.route` says why.
* `NotIncrementalError` (`not_incremental`): a plan has no verified delta
  rules.
* `ConcurrentWriteError` (`concurrent_write`): another process committed to
  a sink while this refresh wrote it; the write was not committed, and the
  next refresh recovers.
* `UnsupportedError` (`unsupported`): sverify refuses the input; the SQL
  lift, the Ibis producer, the checker, the SQL writer and the Polars
  translator all raise it (or a subclass), saying which construct. A
  `ValueError`.
* `SqlError` (`sql_refused`): a SQL producer refused a query.
* `ExportError` (`export_refused`): a plan has no conforming Substrait form
  that keeps its proof (`Report.to_substrait`, #664); the message names the
  reason and the spec gap.

Setup:

* `CheckerVersionError` (`checker_version`): the `substrait-check` binary
  is older or newer than this sverify.
* `EngineVersionError` (`engine_version`), `EngineVersionWarning`: an
  engine's version is not one its profile's facts were probed at (another
  major version refuses).
* `EngineSettingsError` (`engine_settings`), `EngineSettingsWarning`: an
  engine setting differs from the one its profile's facts were probed
  under.

Warnings:

* `SverifyWarning`: the base of every warning below;
  `filterwarnings("error", category=SverifyWarning)` fails a CI job on any.
* `UnverifiedRunWarning`: a plan that is not proved runs, with
  `unverified=True` or `transform(on_unproved="warn")`.
* `UnprovedWarning`: a transform with `on_unproved="warn"` is built
  although its contract is not proved; `.report` has the details.
* `InferredWarning`: an inferred precondition is assumed
  (`on_inferred="warn"`); `.report` has the details.

`Unsupported` and `NotIncremental` are deprecated names of
`UnsupportedError` and `NotIncrementalError`.
"""

import warnings
from typing import Any

from sverify._unsupported import SverifyError, SverifyWarning, UnsupportedError
from sverify.contracts import (
    CompositionError,
    InferredWarning,
    PostconditionError,
    PreconditionError,
    UnprovedWarning,
    UnverifiedRunError,
    VerificationError,
)
from sverify.engine import CheckerVersionError, SqlError
from sverify.incremental import AuditError, NotIncrementalError, SchemaError
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

_DEPRECATED = {"Unsupported": UnsupportedError, "NotIncremental": NotIncrementalError}


def deprecated_name(module: str, name: str) -> Any:
    """`module.name` where `name` is a deprecated name of an exception
    (`_DEPRECATED`), with a `DeprecationWarning`; an `AttributeError`
    otherwise."""
    if name in _DEPRECATED:
        new = _DEPRECATED[name].__name__
        warnings.warn(
            f"{module}.{name} is deprecated; write {module}.{new}",
            DeprecationWarning,
            stacklevel=3,
        )
        return _DEPRECATED[name]
    raise AttributeError(f"module {module!r} has no attribute {name!r}")


def __getattr__(name: str) -> Any:
    return deprecated_name(__name__, name)


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
    "InferredWarning",
    "NotIncrementalError",
    "PostconditionError",
    "PreconditionError",
    "RouteError",
    "SchemaError",
    "SqlError",
    "SverifyError",
    "SverifyWarning",
    "UnprovedWarning",
    "UnsupportedError",
    "UnverifiedRunError",
    "UnverifiedRunWarning",
    "VerificationError",
]

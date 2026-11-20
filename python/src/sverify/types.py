"""The types sverify's public API returns and holds, for annotations and
`isinstance`: the conditions a contract states, what a report says, what
a refresh did, and where a node stands. You get them from sverify; you don't build them.

Conditions, what `sv.unique`, `sv.key`, `sv.references`, `sv.max_rows`,
`sv.rows_per`, `sv.non_overlapping`, `sv.arrives_within` and `sv.approx`
return: `Unique`, `Key`, `References`, `MaxRows`, `RowsPer`,
`NonOverlapping`, `ArrivesWithin` and `Approx`, and a `PlannedCondition`
read back from a Substrait export. `SQLStep` is what `sv.sql` returns.

The report (`sverify.verify`, `Report`):

* `Issue`: a reason a plan is not proved, with the preconditions that
  would settle it (`Needed`).
* `CheckedCondition`: a postcondition and how it was established, with a
  `Counterexample` where the checker found one; `Discharged`: how a
  precondition was established.
* `ColumnFacts`: what the checker proved about a result column
  (`Report.facts`): whether it may be NULL, and bounds on its values.
* `Observation`: what the result's consumer observes (`sv.equivalent`),
  with `Within` tolerances (`sv.within`).
* `Route`: how a plan reaches an engine, or why it doesn't.
* `DialectDifference`: where an engine's SQL dialect differs from the
  semantics a plan was verified under.

Refresh and status (`Node.refresh()`, `Node.status()`, `sv.group`):

* `Refresh` holds a `StageRefresh` per node, each with its
  `RefreshReport` (a `SourceRefresh` per source, `QuarantineReport`s and
  `RetentionReport`s).
* `Status` holds a `NodeStatus` per node; `Group` is what `sv.group`
  returns.

This module only names them; `import sverify` doesn't import it. What is
public is defined in `docs/stability.md`.
"""

from sverify._dialect import DialectDifference
from sverify._quarantine import QuarantineReport
from sverify._retention import RetentionReport
from sverify.conditions import (
    Approx,
    ArrivesWithin,
    CheckedCondition,
    Discharged,
    Key,
    MaxRows,
    NonOverlapping,
    PlannedCondition,
    References,
    RowsPer,
    Unique,
)
from sverify.counterexample import Counterexample
from sverify.incremental import RefreshReport, SourceRefresh
from sverify.nodes import Group, NodeStatus, Refresh, StageRefresh, Status
from sverify.observation import Observation, Within
from sverify.report import ColumnFacts, Issue, Needed
from sverify.routes import Route
from sverify.sql_model import SQLStep

__all__ = [
    "Approx",
    "ArrivesWithin",
    "CheckedCondition",
    "ColumnFacts",
    "Counterexample",
    "DialectDifference",
    "Discharged",
    "Group",
    "Issue",
    "Key",
    "MaxRows",
    "Needed",
    "NodeStatus",
    "NonOverlapping",
    "Observation",
    "PlannedCondition",
    "QuarantineReport",
    "References",
    "Refresh",
    "RefreshReport",
    "RetentionReport",
    "Route",
    "RowsPer",
    "SQLStep",
    "SourceRefresh",
    "StageRefresh",
    "Status",
    "Unique",
    "Within",
]

"""Verified Substrait plans on DataFusion: contracts and incremental views, checked in Lean."""

from sverify.asof import asof_join
from sverify.contracts import (
    Issue,
    PostconditionError,
    PreconditionError,
    Report,
    Unique,
    VerificationError,
    transform,
    unique,
    verify,
)
from sverify.engine import connect, create_table, run_substrait_json, substrait_json, table_rows
from sverify.incremental import Changes, IncrementalView, NotIncremental, delta_plans

__all__ = [
    "asof_join",
    "Issue",
    "PostconditionError",
    "PreconditionError",
    "Report",
    "Unique",
    "VerificationError",
    "transform",
    "unique",
    "verify",
    "Changes",
    "IncrementalView",
    "NotIncremental",
    "connect",
    "create_table",
    "table_rows",
    "delta_plans",
    "run_substrait_json",
    "substrait_json",
]

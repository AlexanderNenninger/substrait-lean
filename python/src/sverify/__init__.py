"""Verified Substrait plans on DataFusion and Polars: contracts and incremental views, checked in
Lean."""

from sverify.asof import asof_join
from sverify.contracts import (
    CompositionError,
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
from sverify.engine import (
    ENGINES,
    connect,
    create_table,
    run_plan,
    run_substrait_json,
    substrait_json,
    table_rows,
    written_plan,
)
from sverify.incremental import Changes, IncrementalView, NotIncremental, delta_plans

__all__ = [
    "CompositionError",
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
    "run_plan",
    "written_plan",
    "ENGINES",
    "substrait_json",
]

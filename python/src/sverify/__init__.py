"""Verified Substrait plans: incremental view maintenance with Lean-checked delta plans."""

from sverify.contracts import (
    PostconditionError,
    PreconditionError,
    Report,
    VerificationError,
    transform,
    verify,
)
from sverify.duck import connect, run_substrait_json, substrait_json
from sverify.incremental import Changes, IncrementalView, NotIncremental, delta_plans

__all__ = [
    "PostconditionError",
    "PreconditionError",
    "Report",
    "VerificationError",
    "transform",
    "verify",
    "Changes",
    "IncrementalView",
    "NotIncremental",
    "connect",
    "delta_plans",
    "run_substrait_json",
    "substrait_json",
]

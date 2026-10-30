"""Verified Substrait plans: incremental view maintenance with Lean-checked delta plans."""

from sverify.duck import connect, run_substrait_json, substrait_json
from sverify.incremental import Changes, IncrementalView, NotIncremental, delta_plans

__all__ = [
    "Changes",
    "IncrementalView",
    "NotIncremental",
    "connect",
    "delta_plans",
    "run_substrait_json",
    "substrait_json",
]

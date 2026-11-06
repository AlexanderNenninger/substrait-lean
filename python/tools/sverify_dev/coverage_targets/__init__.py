"""The coverage targets of sverify 1.0 (#743), one module per area.

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

Each target is a construct real queries use, with a decision: `in` for 1.0,
`skipped` (a hard blocker, with its reason) or `after` 1.0. Its probes, a
DuckDB SQL query and an Ibis case, say whether sverify covers it today.
`docs/coverage-targets.md` is the list with its reasons;

    uv run python -m sverify_dev.coverage --targets

prints the share of `in` targets covered, which is the number to track.
`tests/test_coverage_targets.py` pins each target's `covered`, so a pull
request that covers a target flips it in its area's file.

The areas are those of the add-function skill (.claude/skills/add-function), so
that a batch of work on one area edits one file here.
"""

from __future__ import annotations

from sverify_dev.coverage_targets import (
    aggregates,
    casts,
    core,
    nested,
    relations,
    strings,
    temporal,
    windows,
)
from sverify_dev.coverage_targets._common import Decision, Target, probe

__all__ = ["AREAS", "TARGETS", "Decision", "Target", "probe", "report"]

#: The area modules, in the order of the doc's tables.
AREAS = (relations, core, casts, strings, temporal, nested, aggregates, windows)

TARGETS: list[Target] = [t for m in AREAS for t in m.TARGETS]


def report(probed: dict[str, list[str]] | None = None) -> str:
    """The share of `in` targets covered, by area, and what is left.

    `probed` maps a target's name to its refusals; the probes run when it is
    None."""
    if probed is None:
        probed = {t.name: probe(t) for t in TARGETS}
    ins = [t for t in TARGETS if t.decision == "in"]
    done = [t for t in ins if not probed[t.name]]
    pct = 100 * len(done) // len(ins)
    lines = [
        f"{len(done)} of {len(ins)} constructs in for 1.0 are covered ({pct} %).",
        "",
        "| Area | Covered | Left |",
        "|---|---|---|",
    ]
    for m in AREAS:
        area = [t for t in ins if t.area == m.AREA]
        left = [t for t in area if probed[t.name]]
        names = " · ".join(f"{t.name} (#{t.issue})" if t.issue else t.name for t in left)
        lines.append(f"| {m.AREA} | {len(area) - len(left)} of {len(area)} | {names or '—'} |")
    other = [t for t in TARGETS if t.decision != "in" and not probed[t.name]]
    if other:
        lines += ["", "Skipped or after 1.0, and covered now: " + ", ".join(t.name for t in other)]
    return "\n".join(lines)

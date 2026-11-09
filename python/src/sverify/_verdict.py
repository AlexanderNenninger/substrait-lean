"""The report of a checker answer: `verdict` (#1088).

Internal: not part of sverify's public API. `substrait-check --contract`
answers a request with what it proved (`SubstraitLean/ContractCheck.lean`,
`Realize.lean`); `verdict` is the one place that answer becomes a `Report`.
It reads the checker's fields and decides nothing: which issues are assumed,
which are errors, the class and evidence per engine, the transfer, whether the
result is sorted, the discharged checks, all come from the answer. What the
caller adds is the user's side: the conditions as written, the issues and
facts in the user's terms, the schemas, the hints.

`sverify.verify` (`contracts.py`) and `sverify.from_substrait`
(`substrait_export.recheck`) build their reports here.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from sverify.report import Issue, Report


def verdict(
    out: Mapping[str, Any],
    *,
    request: Mapping[str, Any],
    issues: Sequence[Issue],
    **context: Any,
) -> Report:
    """The report of the checker's answer `out` to `request`.

    Args:
        out: The checker's answer (`substrait-check --contract`'s JSON).
        request: The request it answers.
        issues: `out["issues"]`, one `Issue` each, in the user's terms
            (`contracts._issues`, or as the checker names them).
        **context: The report's fields that are the caller's: `semantics`,
            `requires`, `ensures`, `facts` and the rest. None of them is a
            field the checker decides.

    Returns:
        The report. Its `issues` are the issues, the assumed ones included:
        `split_assumed` moves those to `assumed` once the preconditions are
        final.
    """
    from sverify.conditions import RelationRows
    from sverify.report import Report, tie_places

    semantics = context.get("semantics", "reference")
    return Report(
        issues=list(issues),
        deterministic=out["deterministic"],
        _windows_total=out.get("windows_total", out["deterministic"]),
        _tie_places=tie_places(out),
        _guard_free=out["guard_free"],
        _unchecked=out.get("unchecked"),
        _optimized=out.get("optimized"),
        _rewrites=out.get("rewrites", []),
        rows=out.get("rows"),
        _relations=[
            RelationRows(r["op"], r["depth"], r["rows"], r["group_rows"])
            for r in out.get("relations", [])
        ],
        _depends=out.get("depends"),
        _epsilon=out.get("epsilon"),
        _rows_exact=out.get("rows_exact"),
        _margin_checks=list(out.get("margin_checks") or []),
        _engines=out.get("engines"),
        _sorted=out.get("sorted"),
        _contract=dict(request),
        _transfer=(out.get("transfer") or {}).get("failures") if semantics == "substrait" else None,
        **context,
    )


def split_assumed(report: Report) -> Report:
    """`report` with its assumed issues (`Issue.assumed`, the checker's: a
    `SUM` that may leave its type, an operation on finite doubles that may
    give `±∞`, #575) moved from `issues` to `assumed`: they are checked on the
    data while the job runs."""
    report.assumed = [i for i in report.issues if i.assumed]
    report.issues = [i for i in report.issues if not i.assumed]
    return report

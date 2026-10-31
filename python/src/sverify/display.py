"""Compact tables for marimo notebooks, as the tour in `notebooks/` uses them.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

Tables are small static HTML, so NULL can be dimmed and Z-set weights
coloured green or red, which `mo.ui.table` can't do. Needs marimo, which is
not a dependency of sverify.
"""

import datetime as dt
import math
from collections.abc import Sequence

import marimo as mo

CELL = "text-align:left;padding:4px 16px 4px 0;white-space:nowrap"
PLUS, MINUS = "#2e8b57", "#c0392b"


def show(v: object) -> str:
    """A value as SQL would print it."""
    if v is None:
        return "NULL"
    if v is True:
        return "true"
    if v is False:
        return "false"
    if isinstance(v, float) and math.isnan(v):
        return "NaN"
    if isinstance(v, dt.datetime):
        if v.microsecond:
            return f"{v:%Y-%m-%d %H:%M:%S.%f}"[:-3]
        return f"{v:%Y-%m-%d %H:%M:%S}" if v.second else f"{v:%Y-%m-%d %H:%M}"
    if isinstance(v, str):
        return v
    return repr(v)


def table(
    rows: Sequence[Sequence[object]],
    columns: Sequence[str],
    weights: Sequence[int] | None = None,
    title: str | None = None,
) -> mo.Html:
    """A compact table; NULL is dimmed, weights are green (+) or red (−)."""
    cols = list(columns) + (["weight"] if weights is not None else [])
    head = "".join(f"<th style='{CELL}'>{c}</th>" for c in cols)
    body = []
    for i, r in enumerate(rows):
        cells = "".join(
            f"<td style='{CELL};opacity:.5'>NULL</td>"
            if v is None
            else f"<td style='{CELL}'>{show(v)}</td>"
            for v in r
        )
        if weights is not None:
            w = weights[i]
            color = PLUS if w > 0 else MINUS
            sign = "+" if w > 0 else "−"
            cells += f"<td style='{CELL};color:{color};font-weight:600'>{sign}{abs(w)}</td>"
        body.append(f"<tr>{cells}</tr>")
    if not rows:
        body.append(f"<tr><td colspan='{len(cols)}' style='opacity:.55'><em>(empty)</em></td></tr>")
    html = mo.Html(
        "<table style='border-collapse:collapse;font-size:0.9rem;width:auto;margin:0'>"
        f"<thead><tr>{head}</tr></thead><tbody>{''.join(body)}</tbody></table>"
    )
    return mo.vstack([mo.md(f"**{title}**"), html]) if title else html


def zset(
    z: Sequence[tuple[Sequence[object], int]], columns: Sequence[str], title: str | None = None
):
    """A Z-set (rows with weights) as a table."""
    return table([r for r, _ in z], columns, [w for _, w in z], title)


def arrow(t, title: str | None = None) -> mo.Html:
    """A pyarrow table (or Ibis expression) as a compact table."""
    if hasattr(t, "to_pyarrow"):
        t = t.to_pyarrow()
    return table([tuple(r.values()) for r in t.to_pylist()], t.column_names, title=title)


def side_by_side(*items, gap: float = 2) -> mo.Html:
    return mo.hstack(list(items), justify="start", gap=gap, wrap=True)


def verdict(ok: bool, yes: str, no: str) -> mo.Html:
    return mo.callout(mo.md(yes if ok else no), kind="success" if ok else "danger")

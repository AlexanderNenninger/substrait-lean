"""A raise of the written plan that a reported assumption explains (#2162,
rulings 230 and 233).

Maintainer tooling (`sverify_dev`): not in the wheel.

A written plan raises an `sverify:`-tagged error where an assumed issue it
checks at run time occurs (a `SUM` leaving 64 bits, a cast to 32 bits that
does not fit, an integer operation that wraps). That is the check doing its
job, not a disagreement, when the report lists the issue (`Report.assumed`)
and the Lean checker finds the same issue on the same data
(`lean_assumed`, `--assumed`, or the reference's raise, `--raises`). The
replay (`slt`) and the fuzz (`fuzz`) call `checked` for one class of this
shape; a raise the report does not list, or the checker does not find, stays
a disagreement, and is a soundness-relevant gap to report (ruling 230, C2).
"""

from __future__ import annotations

#: What the written plan's tagged errors say, and the kinds of `Issue` that
#: report the assumption behind them.
TAGS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("integer overflow in SUM", ("SUM overflow",)),
    ("CAST to", ("overflow", "cast out of range")),
    ("overflow", ("overflow",)),
)


def checked(message: str, listed: list[str], plan_with_data: str) -> str | None:
    """`checked: <issue>` if the engine's `message` is a tagged raise of an
    issue `listed` (the `str` of each of the report's errors and assumptions,
    `kind: expression`) holds and the checker finds on `plan_with_data` (the
    written plan with the tables inlined); None otherwise."""
    from sverify._lean_eval import lean_assumed
    from sverify.engine import run_checker

    if "sverify:" not in message:
        return None
    text = message.split("sverify:", 1)[1]
    kinds = next((ks for tag, ks in TAGS if text.strip().startswith(tag)), ())
    named = [a for a in listed if a.split(":", 1)[0] in kinds]
    if not named:
        return None
    # An assumption (`--assumed`) or an issue the reference raises (`--raises`).
    code, out, _ = run_checker(("--raises",), plan_with_data)
    found = lean_assumed(plan_with_data) or (out.strip() if code == 0 else "") or None
    return None if found is None else f"checked: {named[0]} (Lean: {found})"

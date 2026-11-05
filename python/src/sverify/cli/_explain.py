"""`sverify explain <code>`: what a problem's code in `sverify check`'s
output means and how to fix it, so the default output stays short (#744)."""

from __future__ import annotations

CODES: dict[str, str] = {
    "may-be-false": (
        "A postcondition may be FALSE on some output rows that the preconditions allow. "
        "The counterexample, where sverify found one, is such an input. Fix it by stating "
        "in `requires` what the inputs meet (the report's `would hold` line names "
        "preconditions under which it holds), by filtering the rows that break it, or by "
        "relaxing the postcondition."
    ),
    "may-be-null": (
        "A postcondition is never FALSE but may be NULL, where a column it reads is NULL. "
        "State `_.col.notnull()` in `requires` for the columns the report names, or write "
        "the postcondition so NULL passes (`_.x.isnull() | (_.x > 0)`)."
    ),
    "always-false": (
        "A postcondition is FALSE on every row the transform can output. The transform or "
        "the postcondition is wrong: check the comparison's direction and the column."
    ),
    "not-a-key": (
        "A `unique(...)` postcondition: the preconditions do not make those columns a key "
        "of the output. Declare a key of the inputs (`sv.unique(...)` in `requires`) that "
        "the transform keeps, or deduplicate."
    ),
    "ties": (
        "Rows may tie in an ORDER BY (a window, `first`, a LIMIT), so the result is not "
        "determined by the inputs. Order by columns that are unique there; the report's "
        "note names a key of an input that would make the order total."
    ),
    "not-proved-kind": (
        "A condition sverify checks on the data only (`references`, `rows_per`, "
        '`arrives_within`): no proof covers it. With `on_unproved="runtime"` each refresh '
        "checks it on the rows it writes."
    ),
    "unknown": (
        "The checker knows nothing that decides the postcondition. State more about the "
        'inputs in `requires`, or check it on the data with `on_unproved="runtime"`.'
    ),
    "observation": (
        "A postcondition is proved, but depends on what the observation "
        "(`sv.equivalent(...)`) ignores, such as row order or exact doubles."
    ),
    "needs": (
        "sverify inferred a precondition the proof needs, a bound that rules out a runtime "
        'error (an overflow, a division by zero), and `on_inferred="error"` (the default) '
        "does not assume it. `sverify suggest <file> --apply` writes it into `requires=`, "
        "after which each refresh checks it on the data; or rewrite the transform so no "
        "row needs it."
    ),
    "overflow": (
        "An integer operation may leave its type (64 bits for BIGINT). State a bound on "
        "the inputs in `requires` (the report's hint names it), or cast to a wider type "
        "first."
    ),
    "sum-overflow": (
        "A SUM may leave its type. sverify assumes it fits and checks that on the data "
        'while the job runs; with `on_inferred="off"`, state the bound yourself.'
    ),
    "division-by-zero": (
        "A divisor may be 0. State `_.d != 0` in `requires`, or guard the division "
        "(`ibis.ifelse(d == 0, None, n / d)`)."
    ),
    "cast-out-of-range": (
        "A cast may receive a value its target type cannot hold. Bound the value in "
        "`requires`, or cast to a wider type."
    ),
    "negative-exponent": "An integer power may get a negative exponent: bound it in `requires`.",
    "domain-error": (
        "A math function may get an argument outside its domain (the logarithm of 0, the "
        "square root of a negative number): bound it in `requires`, or guard the call."
    ),
    "overflow-to-infinity": (
        "An operation on finite doubles, or their SUM or AVG, may give ±infinity. Bound "
        "the inputs in `requires`."
    ),
    "composition": (
        "A transform's precondition on another transform's result does not follow from "
        "what that transform guarantees. Add it to the producing transform's `ensures` "
        '(and prove it there), or check it on the data with `on_unproved="runtime"`.'
    ),
    "transfer": (
        'Under `semantics="substrait"`, the proof holds for the reference but Substrait '
        "allows more at some option; the report names the options."
    ),
    "floats": (
        "No engine's doubles meet the observation's tolerance. Widen the tolerance in "
        "`sv.equivalent(floats=sv.within(...))`, or cap the rows (`sv.max_rows`)."
    ),
    "unchecked": (
        "The file defines a contracted transform but never applies it, so it has no input "
        "schemas to be proved on. Pipe a source into it (`orders.pipe(paid)`), or test it "
        "with `paid.check(orders={...})`."
    ),
    "refused": (
        "sverify refuses a construct of the file: a function, type or operator outside "
        "its model (`sverify.errors.UnsupportedError`). The message names it. Rewrite it in "
        "what sverify reads, or open an issue."
    ),
    "timeout": (
        "The time budget ran out during proof, planning or checking (not while a refresh "
        "moves data). What was proved before is reported; the rest is not. Raise it with "
        "`--timeout` or `SVERIFY_TIMEOUT` (0 turns it off)."
    ),
    "memory": (
        "DuckDB ran out of its `--memory-limit` (`SVERIFY_MEMORY_LIMIT`) while it ran a "
        "query, after spilling what it could to disk. Nothing was written to a sink. Raise "
        "the limit, or refresh in smaller batches."
    ),
    "error": "The file raised an error of its own while sverify imported it: see the message.",
}


def code_of(kind: str) -> str:
    """A report's reason or issue kind as a code: `may_be_false` is
    `may-be-false`, "division by zero" `division-by-zero`."""
    return kind.strip().lower().replace("_", "-").replace(" ", "-")


def explain(code: str) -> str | None:
    """The explanation of `code`, or None if there is none."""
    return CODES.get(code_of(code))

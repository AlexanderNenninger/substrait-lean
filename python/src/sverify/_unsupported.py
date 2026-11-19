"""`SverifyError`, the base of every exception sverify raises on purpose,
`UnsupportedError`, the one class every refusal of sverify derives from,
and `SverifyWarning`, the base of every warning sverify issues.

Internal module (a leaf, so that every module can import it); the public
names are in `sverify.errors`. `Unsupported` is the internal modules' short
name for `UnsupportedError`; `sverify.errors.Unsupported` is deprecated.
"""

from collections.abc import Mapping
from typing import ClassVar

#: Where #271 is, for refusals: an engine that does not run a function yet.
ISSUE_271 = "see #271, https://github.com/AlexanderNenninger/substrait-lean/issues/271"
#: Where #1725 is: an engine that has no map for a UTC-zoned timestamp (an instant) yet.
ISSUE_1725 = "see #1725, https://github.com/AlexanderNenninger/substrait-lean/issues/1725"
#: The end of a refusal of what only DuckDB runs: its exit.
DUCKDB_ONLY = f"run it with engine='duckdb' ({ISSUE_271})"

#: The start of the message of a RANGE frame's guard (#805): a bound that
#: leaves its integer key's type. An engine whose dialect raises writes it
#: (`ProfilePlugin.guards`).
RANGE_GUARD = "Overflow in a RANGE frame bound"


#: The exit of a refusal of data that breaks a stated condition.
ROWS_HELD = '; to hold the batch instead, use `on_violation="hold"`, or raise the cap'
#: The same, for a condition with a rule for which rows break it.
ROWS_ASIDE = '; to set such rows aside, use `on_violation="quarantine"` or `"hold"`'


class SverifyError(Exception):
    """The base of every exception sverify raises on purpose: a refusal
    (`Unsupported`), a proof that fails (`VerificationError`), data that
    breaks a condition (`PreconditionError`), a route, a sink, an export.
    `except sverify.errors.SverifyError` catches them all; each also keeps
    the built-in base it had (`ValueError`, `RuntimeError`), so existing
    handlers still catch it. Misuse of the API (a wrong argument) raises
    `TypeError` or `ValueError` as usual.

    Attributes:
        code: What failed, as a snake_case code that stays the same across
            1.x (`"not_proved"`, `"unsupported"`, `"precondition_failed"`,
            …): the code the CLI, SARIF and OpenTelemetry report. Each
            subclass sets its own.
    """

    code: ClassVar[str] = "error"


class UnsupportedError(SverifyError, ValueError):
    """Sverify refuses the input: the SQL lift or the Ibis producer cannot
    read it, Lean's model does not cover it, or an engine or SQL dialect
    cannot run it. The message says which construct, and why.

    The SQL lift, the Ibis producer, the SQL writer and the Polars
    translator raise subclasses of it, so `except sverify.errors.UnsupportedError`
    catches every refusal, whichever step made it. It is a `ValueError`.
    """

    code = "unsupported"

    def __init__(self, *args: object, construct: str | None = None, sql: str | None = None):
        super().__init__(*args)
        self.construct = construct
        """The construct refused, as `"function md5"` for a function (its lower-case
        name as the user writes it) and otherwise the SQL keywords in upper case
        (`"WITH RECURSIVE"`, `"IS DISTINCT FROM"`); None where the refusal names none."""
        self.sql = sql
        """The SQL fragment the SQL lift refused; None for the Ibis producer."""


Unsupported = UnsupportedError
"""The internal modules' name for `UnsupportedError`."""


class ConditionError(UnsupportedError):
    """Conditions of `requires` or `ensures` that sverify cannot read: a
    column the table or the result does not have, SQL outside what the lift
    reads, a construct outside the model, an Ibis condition that does not
    type-check or names a column the table lacks. `verify` reads every condition
    before it proves anything and raises once, naming all of them; the query
    itself is not refused. Fix or drop those conditions.
    `sverify.errors.ConditionError`.

    Attributes:
        errors: Each unreadable condition, by its label, with its own
            refusal (an `UnsupportedError`; its message says why).
    """

    code = "condition_unreadable"

    def __init__(self, errors: Mapping[str, UnsupportedError]):
        self.errors = dict(errors)
        listed = "".join(f"\n  {label}: {e}" for label, e in self.errors.items())
        super().__init__(
            f"{len(self.errors)} condition(s) cannot be read:{listed}\n"
            "fix or drop them; the query is not refused"
        )


class SverifyWarning(UserWarning):
    """The base of every warning sverify issues. In a CI job,
    `warnings.filterwarnings("error", category=SverifyWarning)` (or pytest's
    `-W error::sverify.errors.SverifyWarning`) turns each into a failure, and
    nothing else."""

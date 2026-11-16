"""`SverifyError`, the base of every exception sverify raises on purpose,
`UnsupportedError`, the one class every refusal of sverify derives from,
and `SverifyWarning`, the base of every warning sverify issues.

Internal module (a leaf, so that every module can import it); the public
names are in `sverify.errors`. `Unsupported` is the internal modules' short
name for `UnsupportedError`; `sverify.errors.Unsupported` is deprecated.
"""

from typing import ClassVar

#: Where #271 is, for refusals: an engine that does not run a function yet.
ISSUE_271 = "see #271, https://github.com/AlexanderNenninger/substrait-lean/issues/271"
#: The end of a refusal of what only DuckDB runs: its exit.
DUCKDB_ONLY = f"run it with engine='duckdb' ({ISSUE_271})"

#: The start of the message of a RANGE frame's guard (#805): a bound that
#: leaves its integer key's type. An engine whose dialect raises writes it
#: (`ProfilePlugin.guards`).
RANGE_GUARD = "Overflow in a RANGE frame bound"


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


Unsupported = UnsupportedError
"""The internal modules' name for `UnsupportedError`."""


class SverifyWarning(UserWarning):
    """The base of every warning sverify issues. In a CI job,
    `warnings.filterwarnings("error", category=SverifyWarning)` (or pytest's
    `-W error::sverify.errors.SverifyWarning`) turns each into a failure, and
    nothing else."""

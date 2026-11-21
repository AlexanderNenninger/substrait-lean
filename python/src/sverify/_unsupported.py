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
#: Why a quantile of a DECIMAL is refused (by design, ruling 191, #1921): both
#: frontends say it, each adding its own way out (`CAST(x AS DOUBLE)`,
#: `x.cast('float64')`).
QUANTILE_OF_DECIMAL = (
    "is not supported: no engine gives one value for it (DuckDB truncates a double "
    "interpolation, Spark and Polars return doubles)"
)
#: Why DuckDB refuses the text of a `DECIMAL(38, 38)` (D72, ruling 245): it prints a
#: `DECIMAL(p, p)` without its integer part, and has no wider type to print this one from.
DECIMAL_38_38 = (
    "a DECIMAL(38, 38) cast to VARCHAR is not supported on DuckDB: DuckDB prints it without its "
    "integer part and has no wider decimal to print it from; cast it to DECIMAL(38, 37) first"
)
#: The end of a refusal of what only DuckDB runs: its exit.
DUCKDB_ONLY = f"run it with engine='duckdb' ({ISSUE_271})"

#: The start of the message of a RANGE frame's guard (#805): a bound that
#: leaves its integer key's type. An engine whose dialect raises writes it
#: (`ProfilePlugin.guards`).
RANGE_GUARD = "Overflow in a RANGE frame bound"
#: The message of the integer `%` guard under `semantics="duckdb"` (#2058): DuckDB
#: raises at `MIN % -1`, where the reference's remainder, 0, fits. DuckDB,
#: Spark and Polars run it (`ProfilePlugin.guards`).
MIN_MOD_GUARD = "integer overflow: MIN % -1"


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
        """The SQL fragment the SQL lift refused, as the lift writes it (shortened): the
        innermost node being read, or the node a whole-query check found. None for the Ibis
        producer, and for a refusal about the query as a whole (its syntax, a clause)."""


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


class MemoryLimitError(SverifyError, MemoryError):
    """A step ran out of the memory sverify or the engine allows it (#783):
    the checker past its cap during a proof, or DuckDB past its
    `memory_limit` during a run or a refresh. A refresh that raises it
    commits nothing. The engine's own exception is the `__cause__`.
    A `MemoryError`."""

    code = "memory_limit"

    def __init__(self, message: str, *, stage: str, limit: str, setting: str):
        super().__init__(message)
        self.stage = stage
        """Where it ran out: `"proof"`, `"run"` or `"refresh"`."""
        self.limit = limit
        """The limit in force, as text (`"2.0 GiB"`, `"4096 MB"`)."""
        self.setting = setting
        """The setting that raises the limit: `SVERIFY_MEMORY_LIMIT` (the data's
        engine) or `SVERIFY_CHECKER_MEMORY_MB` (the checker)."""


class SverifyWarning(UserWarning):
    """The base of every warning sverify issues. In a CI job,
    `warnings.filterwarnings("error", category=SverifyWarning)` (or pytest's
    `-W error::sverify.errors.SverifyWarning`) turns each into a failure, and
    nothing else."""

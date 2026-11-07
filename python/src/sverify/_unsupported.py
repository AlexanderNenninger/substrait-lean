"""`SverifyError`, the base of every exception sverify raises on purpose,
and `Unsupported`, the one class every refusal of sverify derives from.

Internal module (a leaf, so that every module can import it); the public
names are `sverify.errors.SverifyError`, `sverify.errors.Unsupported` and
`sverify.engines.Unsupported`.
"""

#: The refusal of a window `SUM`, `AVG`, `VARIANCE` or `STDDEV` of doubles:
#: the plan's bound leaves out window functions, so the result would pass as
#: exact where the engine's value differs from the reference's.
WINDOW_FLOAT_AGG = (
    "a window SUM, AVG, VARIANCE or STDDEV of doubles has no bound yet "
    "(see #1032, https://github.com/AlexanderNenninger/substrait-lean/issues/1032)"
)


class SverifyError(Exception):
    """The base of every exception sverify raises on purpose: a refusal
    (`Unsupported`), a proof that fails (`VerificationError`), data that
    breaks a condition (`PreconditionError`), a route, a sink, an export.
    `except sverify.errors.SverifyError` catches them all; each also keeps
    the built-in base it had (`ValueError`, `RuntimeError`), so existing
    handlers still catch it. Misuse of the API (a wrong argument) raises
    `TypeError` or `ValueError` as usual."""


class Unsupported(SverifyError, ValueError):
    """Sverify refuses the input: the SQL lift or the Ibis producer cannot
    read it, Lean's model does not cover it, or an engine or SQL dialect
    cannot run it. The message says which construct, and why.

    The SQL lift, the Ibis producer, the SQL writer and the Polars
    translator raise subclasses of it, so `except sverify.errors.Unsupported`
    catches every refusal, whichever step made it. It is a `ValueError`.
    """

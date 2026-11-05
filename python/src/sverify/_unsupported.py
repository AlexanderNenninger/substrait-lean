"""`Unsupported`, the one class every refusal of sverify derives from.

Internal module (a leaf, so that every module can import it); the public
names are `sverify.errors.Unsupported` and `sverify.engines.Unsupported`.
"""


class Unsupported(ValueError):
    """Sverify refuses the input: the SQL lift or the Ibis producer cannot
    read it, Lean's model does not cover it, or an engine or SQL dialect
    cannot run it. The message says which construct, and why.

    The SQL lift, the Ibis producer, the SQL writer and the Polars
    translator raise subclasses of it, so `except sverify.errors.Unsupported`
    catches every refusal, whichever step made it. It is a `ValueError`.
    """

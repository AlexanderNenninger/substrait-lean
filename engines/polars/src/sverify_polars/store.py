"""Polars's store, for now (#1189, interim): its views' state as Arrow
tables in the Python process, with the operations of `sverify._arrow_state`,
until a Polars frame holds it keeps it natively (`PolarsStore`).
"""

from __future__ import annotations

from sverify._arrow_state import ArrowOps


class ArrowStore(ArrowOps):
    """Polars's views' state as Arrow tables in the Python process."""

"""SQL from verified Substrait plans: `to_sql(plan, dialect)`; see `sverify.sql.core`.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.
"""

from typing import Any

from sverify._engines import DIALECTS
from sverify.sql.core import Dialect, Kind, Unsupported, parse_plan, to_sql


def dialect_of(dialect: Any) -> Dialect:
    """The `Dialect` named `dialect` (an installed engine's, `DIALECTS`:
    `"duckdb"`, `"snowflake"`, `"spark"`), or `dialect` itself when it is
    one.

    Raises:
        ValueError: `dialect` names no dialect.
    """
    if isinstance(dialect, Dialect):
        return dialect
    from sverify import profiles

    p = profiles.find(dialect) if isinstance(dialect, str) else None
    if p is None or p.dialect is None:
        raise ValueError(f"unknown dialect {dialect!r}; expected one of {DIALECTS} or a Dialect")
    return p.dialect()


__all__ = ["DIALECTS", "Dialect", "Kind", "Unsupported", "dialect_of", "parse_plan", "to_sql"]

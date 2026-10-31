"""SQL from verified Substrait plans: `to_sql(plan, dialect)`; see `sverify.sql.core`.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.
"""

from sverify.sql.core import Dialect, Kind, Unsupported, parse_plan, to_sql

__all__ = ["Dialect", "Kind", "Unsupported", "parse_plan", "to_sql"]

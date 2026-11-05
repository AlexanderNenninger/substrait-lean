"""SQL from verified Substrait plans: `to_sql(plan, dialect)`; see `sverify.sql.core`.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.
"""

from typing import Any

from sverify.sql.core import Dialect, Kind, Unsupported, parse_plan, to_sql

DIALECTS = ("duckdb", "snowflake", "spark")


def dialect_of(dialect: Any) -> Dialect:
    """The `Dialect` named `dialect` (`"duckdb"`, `"snowflake"` or
    `"spark"`), or `dialect` itself when it is one.

    Raises:
        ValueError: `dialect` names no dialect.
    """
    if isinstance(dialect, Dialect):
        return dialect
    if dialect == "duckdb":
        from sverify.sql.duckdb import DUCKDB

        return DUCKDB
    if dialect == "snowflake":
        from sverify.sql.snowflake import SNOWFLAKE

        return SNOWFLAKE
    if dialect == "spark":
        from sverify.sql.spark import SPARK

        return SPARK
    raise ValueError(f"unknown dialect {dialect!r}; expected one of {DIALECTS} or a Dialect")


__all__ = ["DIALECTS", "Dialect", "Kind", "Unsupported", "dialect_of", "parse_plan", "to_sql"]

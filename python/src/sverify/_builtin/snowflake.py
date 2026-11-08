"""Snowflake's SQL dialect (`sverify.sql.snowflake`). Its profile, with its
translation and checker, is a package of its own from the private evidence
repository, merged with this entry field by field (`sverify.profiles`).
"""

from __future__ import annotations

from typing import Any

from sverify.profiles import ProfilePlugin


def _dialect() -> Any:
    from sverify.sql.snowflake import SNOWFLAKE

    return SNOWFLAKE


PLUGIN = ProfilePlugin("snowflake", dialect=_dialect)

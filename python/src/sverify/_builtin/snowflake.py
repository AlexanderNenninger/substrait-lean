"""Snowflake's SQL dialect (`sverify.sql.snowflake`). Its profile, with its
translation and checker, is a package of its own from the private evidence
repository, merged with this entry field by field (`sverify.profiles`).
"""

from __future__ import annotations

from typing import Any

from sverify._unsupported import ISSUE_271, RANGE_GUARD
from sverify.profiles import ProfilePlugin


def _dialect() -> Any:
    from sverify.sql.snowflake import SNOWFLAKE

    return SNOWFLAKE


PLUGIN = ProfilePlugin(
    "snowflake",
    dialect=_dialect,
    title="Snowflake",
    refuses={
        "sverify_raise": (
            "Snowflake's SQL of the date guards grows past what it runs: a date from "
            "columns writes 208 MB of nested CASEs",
            ISSUE_271,
        )
    },
    guards=(RANGE_GUARD,),
)

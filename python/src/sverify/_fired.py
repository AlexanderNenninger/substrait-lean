"""Whether an engine's error is a run-time check of the plan firing (ruling 258).

A plan's run-time checks (the guards that raise, `Dialect.raise_`, and
Polars's `RuntimeIssue`) stop a run on data that breaks a condition the proof
assumed, before anything is committed. A refresh holds such a node; any other
error stays an error. This is the one place that tells the two apart.
"""

from __future__ import annotations

import re

from sverify.errors import SverifyError

#: The text a SQL engine's guard raises: `sverify: <message>: <value>`
#: (`Dialect.raise_` of DuckDB, Spark and Snowflake). The value is data, so
#: only the message is kept.
_GUARD = re.compile(r"sverify: (?P<message>[^:\n]+): ")


def fired_check(error: BaseException) -> str | None:
    """What a run-time check that fired says, without the data it fired on,
    or None where `error` is not one (a crash, I/O, a sverify error).

    Polars raises `sverify_polars.RuntimeIssue`, whose `issue` names the check;
    the SQL engines raise their own error whose text carries the writer's
    `sverify: ` message.
    """
    for e in (error, error.__cause__):
        if e is None or isinstance(e, SverifyError):
            continue
        for cls in type(e).__mro__:
            if cls.__name__ == "RuntimeIssue" and cls.__module__.startswith("sverify_polars"):
                return str(getattr(e, "issue", "a run-time check"))
        if m := _GUARD.search(str(e)):
            return m["message"]
    return None

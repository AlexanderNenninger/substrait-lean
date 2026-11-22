"""Whether an engine's error is a run-time check of the plan firing (ruling 258).

A plan's run-time checks (the guards that raise, `Dialect.raise_`, and
Polars's `RuntimeIssue`) stop a run on data that breaks a condition the proof
assumed, before anything is committed. A refresh holds such a node; any other
error stays an error. This is the one place that tells the two apart.
"""

from __future__ import annotations

import re

from sverify._unsupported import SverifyError

#: What each SQL engine raises for the writer's guard, anchored at the start of
#: the error's text: the guard writes `sverify: <message>: <value>` and the
#: engine puts its own prefix before it (`Dialect.raise_`). Anchoring matters:
#: DuckDB quotes the SQL around another error's position, and that SQL contains
#: the guard's literal. The value is data, so only the message is kept.
_GUARDS = (
    re.compile(r"\AInvalid Input Error: sverify: (?P<message>[^:\n]+): "),  # DuckDB
    re.compile(r"\A\[USER_RAISED_EXCEPTION\] sverify: (?P<message>[^:\n]+): "),  # Spark
    re.compile(r"\A[^\n]{0,120}?\bvalue 'sverify: (?P<message>[^:\n']+): "),  # Snowflake's cast
)


def fired_check(error: BaseException) -> str | None:
    """What a run-time check that fired says, without the data it fired on,
    or None where `error` is not one (a crash, I/O, a sverify error).

    Polars raises `sverify_polars.RuntimeIssue`, whose `issue` names the check;
    the SQL engines raise their own error whose text starts with the writer's
    `sverify: ` message behind the engine's prefix.
    """
    for e in (error, error.__cause__):
        if e is None or isinstance(e, SverifyError):
            continue
        for cls in type(e).__mro__:
            if cls.__name__ == "RuntimeIssue" and cls.__module__.startswith("sverify_polars"):
                return str(getattr(e, "issue", "a run-time check"))
        for guard in _GUARDS:
            if m := guard.match(str(e)):
                return m["message"]
    return None

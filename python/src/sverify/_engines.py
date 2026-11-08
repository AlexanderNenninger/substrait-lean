"""The engines sverify names, from the installed plugins (#1166, #1189).

Internal: not part of sverify's public API. Every engine, sverify's own
among them, is a `ProfilePlugin` registered under `sverify.profiles`
(`sverify._builtin`); the sets the rest of sverify reads are derived from
them here, once, when sverify is imported. Which engines have a profile of
their own is the checker's (`substrait-check --options`, `"profiles"`);
`tests/test_engines_table.py` checks the types that name them (`Engine`,
`Semantics`) against it.
"""

from __future__ import annotations

from collections.abc import Mapping

from sverify.profiles import plugins

_FOUND = plugins()

#: The engines a `Connection` runs plans on within the 1.x promise
#: (`sverify.engines.ENGINES`).
LOCAL: tuple[str, ...] = tuple(e for e, p in _FOUND.items() if p.local and not p.optional)
#: The engines a `Connection` accepts: `LOCAL` and the optional ones.
ACCEPTED: tuple[str, ...] = tuple(e for e, p in _FOUND.items() if p.local)
#: The dialects `to_sql` writes.
DIALECTS: tuple[str, ...] = tuple(e for e, p in _FOUND.items() if p.dialect)
#: Every engine sverify names: a row of `_support.SUPPORT` names only these.
NAMED: frozenset[str] = frozenset(_FOUND)
#: The modules each engine needs.
MODULES: Mapping[str, tuple[str, ...]] = {e: p.modules for e, p in _FOUND.items()}


def translations() -> dict[str, str]:
    """The translation from the reference to each engine that has one of its
    own, with what makes it sound: every engine a route may reach."""
    return {e: p.translation for e, p in plugins().items() if p.translation}

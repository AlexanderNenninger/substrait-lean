"""Substrait's own profile (#444): the looseness its extension YAMLs state.

Internal: not part of sverify's public API. A plan verified under it
(`verify(semantics="substrait")`) is checked under `Profile.substrait`, and
the report says whether the reference's proof carries over (`transfer`). It
runs on no engine and writes no SQL.
"""

from __future__ import annotations

from sverify.profiles import ProfilePlugin

PLUGIN = ProfilePlugin("substrait", title="Substrait", profile=True)

"""Deprecated aliases of attributes that became internal or were renamed
before 1.0 (the 1.0 API review, #795): each reads and
writes the new attribute with a `DeprecationWarning`, for one release."""

from __future__ import annotations

import warnings
from typing import Any


def alias(old: str, new: str) -> property:
    """A property `old` that reads and writes the attribute `new`; its
    warning names the instance's class."""

    def message(self: Any) -> str:
        owner = type(self).__name__
        if new.startswith("_"):
            return f"{owner}.{old} is internal and goes in the next release"
        return f"{owner}.{old} is deprecated; read {owner}.{new}"

    def get(self: Any) -> Any:
        warnings.warn(message(self), DeprecationWarning, stacklevel=2)
        return getattr(self, new)

    def set_(self: Any, value: Any) -> None:
        warnings.warn(message(self), DeprecationWarning, stacklevel=2)
        setattr(self, new, value)

    return property(get, set_, doc=f"Deprecated: `{new}`.")


def add(cls: type, names: dict[str, str]) -> None:
    """Add `alias` for each old name and its new name to `cls`."""
    for old, new in names.items():
        setattr(cls, old, alias(old, new))

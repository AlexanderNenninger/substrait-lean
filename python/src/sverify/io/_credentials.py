"""The credentials each node uses (#778): by name, for reading or writing,
and whether the place lies inside what the credential may touch.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release. The
public name `CredentialUse` is re-exported by `sverify.io`.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any, Literal

from sverify.io._common import has_userinfo, public_uri
from sverify.io._secrets import Secret
from sverify.io._storage import Storage

Access = Literal["read", "write"]

DEFAULT = "default chain"
"""The name of the credentials a store finds itself (environment, profile,
role, a CI job's OIDC login)."""
INLINE = "inline values"
"""The name of options or a token given as values: they travel with the
source or sink, and `sverify check` says so."""


@dataclass(frozen=True)
class CredentialUse:
    """One credential a node uses: its name, never a value.

    Attributes:
        table: The source's or sink's name.
        credential: The credential's name or reference (`sverify.io.Secret`),
            "default chain" for what the store finds itself, or "inline
            values" for options given as values.
        access: "read" or "write".
        location: Where: the table's URI, a catalog identifier or a server.
        in_scope: Whether `location` lies inside what the credential may
            read or write (`Storage(reads=, writes=)`), or None when that
            is not known.
    """

    table: str
    credential: str
    access: Access
    location: str | None = None
    in_scope: bool | None = None

    def to_dict(self) -> dict[str, Any]:
        """The use as JSON values."""
        return {
            "table": self.table,
            "credential": self.credential,
            "access": self.access,
            "location": self.location,
            "in_scope": self.in_scope,
        }

    def __str__(self) -> str:
        where = f" ({self.location})" if self.location else ""
        out = f"{self.access}s {self.table}{where} with {self.credential}"
        return out + (" (outside its scope)" if self.in_scope is False else "")


def _given(obj: Any) -> str | None:
    """Where the source or sink is, as the user wrote it."""
    for attr in ("uri", "location", "identifier", "path"):
        v = getattr(obj, attr, None)
        if isinstance(v, str) and v:
            return v
    return None


def _inside(location: str, prefixes: tuple[str, ...]) -> bool:
    loc = location.rstrip("/") + "/"
    return any(loc.startswith(p if p.endswith("/") else p + "/") or loc == p for p in prefixes)


def _scope(storage: Storage, location: str | None, access: Access) -> bool | None:
    if location is None:
        return None
    reads, writes = storage.reads, storage.writes
    if access == "write":
        return None if writes is None else _inside(location, writes)
    if reads is None and writes is None:
        return None
    return _inside(location, (*(reads or ()), *(writes or ())))


def uses(obj: Any, access: Access) -> list[CredentialUse]:
    """The credentials a source or sink uses, by name.

    It reads what sverify's own sources and sinks hold: `storage_options`
    (a `Storage`, a mapping, a function), a Flight source's `secret` or
    token, an Iceberg table's catalog, and the `credentials` a custom
    source or sink declares."""
    name = getattr(obj, "name", type(obj).__name__)
    given = _given(obj)
    location = None if given is None else public_uri(given)
    in_uri = given is not None and has_userinfo(given)
    out: list[CredentialUse] = []

    def add(credential: str, in_scope: bool | None = None) -> None:
        out.append(CredentialUse(name, credential, access, location, in_scope))

    if hasattr(obj, "storage_options"):
        opts = obj.storage_options
        if isinstance(opts, Storage):
            add(opts.label, _scope(opts, location, access))
        elif callable(opts):
            add(getattr(opts, "__qualname__", type(opts).__name__))
        elif isinstance(opts, Mapping) and opts:
            secrets = [v.ref for v in opts.values() if isinstance(v, Secret)]
            plain = len(secrets) < len(opts)
            for s in secrets:
                add(s)
            if plain and not secrets:
                add(INLINE)
        elif location is not None and "://" in location and not in_uri:
            add(DEFAULT)
    if isinstance(getattr(obj, "secret", None), Secret):
        add(obj.secret.ref)
    elif getattr(obj, "token", None):
        add(INLINE)
    catalog = getattr(obj, "catalog", None)
    if catalog is not None and hasattr(catalog, "load_table"):
        add(f"catalog {getattr(catalog, 'name', type(catalog).__name__)}")
    for s in getattr(obj, "credentials", None) or ():
        add(s.ref if isinstance(s, Secret) else str(s))
    if in_uri and all(u.credential != INLINE for u in out):
        add(INLINE)
    return out


def declared(credentials: Any) -> tuple[Secret, ...]:
    """The `credentials=` a custom source or sink declares, as secrets."""
    if credentials is None:
        return ()
    if isinstance(credentials, str | Secret):
        credentials = [credentials]
    return tuple(Secret(c) for c in credentials)

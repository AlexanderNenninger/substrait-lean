"""Object store options shared by sources and sinks, with credentials that
are named, resolved when a table is opened, and kept out of `repr`.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release. The
public name `Storage` is re-exported by `sverify.io`.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping, Sequence
from typing import Any, Union

from sverify.io._secrets import Secret, as_secret, current, resolve_values

Options = Union[Mapping[str, Any], Callable[[], Mapping[str, str]], "Storage", None]


class Storage:
    """Options for the object store tables live in (credentials, region,
    endpoint), given once and passed to every source and sink that needs
    them: `DeltaSource(uri, storage_options=s3)`.

    Credentials go by name: `credentials="lake"` (or a reference
    such as `"bao:kv/pipelines/lake"`) is a `Secret` whose fields are
    options, read when a table is opened; an option's value can be a
    `Secret` too. Without credentials the store's default chain applies
    (environment variables, `~/.aws` profiles, instance or pod roles, the
    OIDC login of a CI job), which is what a pipeline should prefer.
    `options` can also be a function returning a fresh mapping, called
    every time a table is opened, so a long-running job can renew an
    expiring token. sverify keeps no value, and `repr` shows option and
    credential names only.

    `reads` and `writes` declare what the credential may touch, as URI
    prefixes; a named credential's configuration can declare them
    instead (`Resolver`). `sverify check` warns about a sink outside
    `writes` and a source outside `reads` and `writes`.

    The options are delta-rs's (`deltalake`'s `storage_options`), such as
    `AWS_REGION`, `AWS_ACCESS_KEY_ID`, `AWS_SECRET_ACCESS_KEY`,
    `AWS_SESSION_TOKEN`, `GOOGLE_SERVICE_ACCOUNT` or `AZURE_STORAGE_ACCOUNT_NAME`.
    A source or sink of your own can take a `Storage` too and call
    `options()`, and so can an Iceberg catalog:
    `load_catalog("lake", **Storage({"token": Secret("bao:kv/rest#token")}).options())`.

    Args:
        options: The options, values or `Secret`s, or a function returning
            them. Default: none.
        credentials: A secret whose fields are options, by name or
            reference. Default: none, the store's default chain.
        reads: URI prefixes the credentials may read. Default: the
            configuration's for a named credential, else unknown.
        writes: URI prefixes the credentials may write. Default: likewise.
        name: The credential's name in reports when `credentials` is not
            given, such as the CI role's. Default: "default chain".

    Examples:
        ```python
        from sverify.io import DeltaSink, DeltaSource, Secret, Storage

        s3 = Storage(
            {"AWS_REGION": "eu-central-1", "AWS_SECRET_ACCESS_KEY": Secret("env:LAKE_KEY")},
            writes=["s3://lake/marts/"],
        )
        lake = Storage(credentials="lake")   # [tool.sverify.secrets.names] lake = ...
        orders = DeltaSource("s3://lake/orders", storage_options=lake)
        sink = DeltaSink("s3://lake/marts/paid", storage_options=s3)
        ```
    """

    def __init__(
        self,
        options: Mapping[str, Any] | Callable[[], Mapping[str, str]] | None = None,
        *,
        credentials: str | Secret | None = None,
        reads: Sequence[str] | None = None,
        writes: Sequence[str] | None = None,
        name: str | None = None,
    ):
        self._options = options
        self.credentials = as_secret(credentials, "Storage(credentials=)")
        self._reads = None if reads is None else tuple(reads)
        self._writes = None if writes is None else tuple(writes)
        self._name = name

    def options(self) -> dict[str, str]:
        """The options now: the credentials' fields, then the mapping (or
        what the function returns), with every `Secret` read.

        Returns:
            A new dict of options.

        Raises:
            SecretError: A secret cannot be read.
        """
        got = self._options() if callable(self._options) else self._options
        out = self.credentials.fields() if self.credentials is not None else {}
        out.update(resolve_values(got or {}))
        return out

    def secrets(self) -> list[Secret]:
        """The secrets the options name: `credentials`, then the `Secret`
        values in the order given (none for a function)."""
        out = [self.credentials] if self.credentials is not None else []
        if isinstance(self._options, Mapping):
            out += [v for v in self._options.values() if isinstance(v, Secret)]
        return out

    @property
    def label(self) -> str:
        """The credential's name in reports: `credentials`, `name`, the
        function's name, or "default chain"."""
        if self.credentials is not None:
            return self.credentials.ref
        if self._name:
            return self._name
        if callable(self._options):
            return getattr(self._options, "__qualname__", type(self._options).__name__)
        secrets = self.secrets()
        return ", ".join(s.ref for s in secrets) if secrets else "default chain"

    @property
    def reads(self) -> tuple[str, ...] | None:
        """The prefixes the credentials may read, if known."""
        if self._reads is None and self.credentials is not None:
            return current().scope(self.credentials)[0] or None
        return self._reads

    @property
    def writes(self) -> tuple[str, ...] | None:
        """The prefixes the credentials may write, if known."""
        if self._writes is None and self.credentials is not None:
            return current().scope(self.credentials)[1] or None
        return self._writes

    def __repr__(self) -> str:
        parts = []
        if self.credentials is not None:
            parts.append(f"credentials={self.credentials.ref}")
        if callable(self._options):
            parts.append(getattr(self._options, "__qualname__", type(self._options).__name__))
        elif self._options:
            parts.append(", ".join(sorted(self._options)))
        return f"Storage({'; '.join(parts)})"


def resolve(options: Options) -> dict[str, str] | None:
    """The options a source or sink was given, now: None for none."""
    if options is None:
        return None
    if isinstance(options, Storage):
        return options.options()
    got = options() if callable(options) else options
    return resolve_values(got)

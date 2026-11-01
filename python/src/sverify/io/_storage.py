"""Object store options shared by sources and sinks, with credentials that
can be refreshed and are kept out of `repr`.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release. The
public name `Storage` is re-exported by `sverify.io`.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from typing import Union

Options = Union[Mapping[str, str], Callable[[], Mapping[str, str]], "Storage", None]


class Storage:
    """Options for the object store tables live in (credentials, region,
    endpoint), given once and passed to every source and sink that needs
    them: `DeltaSource(uri, storage_options=s3)`.

    `options` is either a fixed mapping or a function returning a fresh one,
    called every time a table is opened, so a long-running job can renew an
    expiring token. sverify keeps no result of that function, and `repr`
    shows option names, never values. Prefer what the store's default chain
    finds (environment variables, `~/.aws` profiles, instance or pod roles)
    or a function that fetches short-lived credentials over literal keys,
    which travel with any object holding them.

    The options are delta-rs's (`deltalake`'s `storage_options`), such as
    `AWS_REGION`, `AWS_ACCESS_KEY_ID`, `AWS_SECRET_ACCESS_KEY`,
    `AWS_SESSION_TOKEN`, `GOOGLE_SERVICE_ACCOUNT` or `AZURE_STORAGE_ACCOUNT_NAME`.
    A source or sink of your own can take a `Storage` too and call `options()`.

    Args:
        options: The options, or a function returning them. Default: none,
            the store's default chain.

    Examples:
        ```python
        import boto3
        from sverify.io import DeltaSink, DeltaSource, Storage


        def credentials():
            c = boto3.Session().get_credentials().get_frozen_credentials()
            return {
                "AWS_REGION": "eu-central-1",
                "AWS_ACCESS_KEY_ID": c.access_key,
                "AWS_SECRET_ACCESS_KEY": c.secret_key,
                "AWS_SESSION_TOKEN": c.token or "",
            }


        s3 = Storage(credentials)
        orders = DeltaSource("s3://lake/orders", storage_options=s3)
        sink = DeltaSink("s3://lake/paid", storage_options=s3)
        ```
    """

    def __init__(self, options: Mapping[str, str] | Callable[[], Mapping[str, str]] | None = None):
        self._options = options

    def options(self) -> dict[str, str]:
        """The options now: the mapping, or what the function returns.

        Returns:
            A new dict of options.
        """
        got = self._options() if callable(self._options) else self._options
        return dict(got or {})

    def __repr__(self) -> str:
        if callable(self._options):
            fn = getattr(self._options, "__qualname__", type(self._options).__name__)
            return f"Storage({fn})"
        return f"Storage({', '.join(sorted(self._options or {}))})"


def resolve(options: Options) -> dict[str, str] | None:
    """The options a source or sink was given, now: None for none."""
    if options is None:
        return None
    if isinstance(options, Storage):
        return options.options()
    got = options() if callable(options) else options
    return dict(got)

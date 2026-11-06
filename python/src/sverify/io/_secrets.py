"""Secrets by name (#775): a `Secret` names where a credential lives, and a
`Resolver` looks it up when a source, sink or catalog needs it.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release. The
public names `Secret`, `Resolver` and `set_resolver` are re-exported by
`sverify.io`, and `SecretError` by `sverify.errors`.

A secret's value never enters an object sverify keeps, a `repr`, a report,
a log or an exception: only its reference does. The backends' own errors
are replaced by one that names the reference and the error's type, raised
outside the `except` block so that no `__context__` carries the original.
"""

from __future__ import annotations

import json
import os
import re
import threading
import time
from collections.abc import Callable, Mapping
from pathlib import Path
from typing import Any, Protocol

from sverify._unsupported import SverifyError

Value = str | Mapping[str, str]
"""What a backend returns for a path: one value, or named fields."""


class SecretError(SverifyError, LookupError):
    """A secret could not be resolved: its name is not configured, its
    backend is not installed or refused, or it has no such field. The
    message names the reference, never a value."""

    code = "secret_unreadable"


class Refused(Exception):
    """A backend's refusal whose message holds no value (an HTTP status, a
    missing setting): the resolver passes its text on."""


_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_.\-]{0,127}")
_SCHEME = re.compile(r"([a-z][a-z0-9\-]*):(.+)", re.S)


class Backend(Protocol):
    """Where secrets live: `get(path)` returns the value at `path`, a string
    or a mapping of fields. Register one with `Resolver(backends=...)`."""

    def get(self, path: str) -> Value: ...


class Secret:
    """A secret, by reference: where its value lives, never the value.

    A reference is `scheme:path`, with `#field` to pick one field of a
    secret that holds several:

    | Reference | Where |
    |---|---|
    | `env:NAME` | the variable `NAME`; `env:PREFIX_*`: those with the prefix, as fields |
    | `file:/run/secrets/token` | a file's text; a JSON object or `KEY=value` lines give fields |
    | `bao:kv/pipelines/lake#token` | OpenBao's KV store (`vault:` for Vault, the same API) |
    | `aws-sm:prod/lake#secret_key` | AWS Secrets Manager (`sverify[secrets-aws]`) |
    | `gcp-sm:projects/p/secrets/lake` | Google Secret Manager (`sverify[secrets-gcp]`) |
    | `azure-kv:my-vault/lake` | Azure Key Vault (`sverify[secrets-azure]`) |
    | `keychain:service/account` | the OS keychain (`sverify[secrets-keychain]`) |

    A bare name such as `"lake"` is looked up in the configuration
    (`Resolver`): its `names` table maps it to a reference, else the
    default backend reads it (by default the environment, `lake` as
    `LAKE`, `flight-token` as `FLIGHT_TOKEN`).

    `repr` and `str` show the reference. The value is read when asked for,
    each time (`value`, `fields`), through the resolver `set_resolver`
    installed, by default the one the configuration describes.

    Args:
        ref: A name or a reference.

    Raises:
        SecretError: `ref` is neither a name nor a reference. The message
            does not repeat it, in case it is a value given by mistake.

    Examples:
        ```python
        import os
        from sverify.io import Secret

        os.environ["EXAMPLE_TOKEN"] = "test-value"
        token = Secret("env:EXAMPLE_TOKEN")
        print(token)          # env:EXAMPLE_TOKEN
        assert token.value() == "test-value"
        ```
    """

    __slots__ = ("ref",)
    ref: str
    """The name or reference."""

    def __init__(self, ref: str | Secret):
        if isinstance(ref, Secret):
            ref = ref.ref
        if not isinstance(ref, str) or not (_NAME.fullmatch(ref) or _reference(ref)):
            raise SecretError(
                "a secret is a name (letters, digits, '_', '-', '.') or a reference "
                "such as 'env:NAME' or 'bao:kv/path#field'; the string given is neither "
                "(it is not repeated here, in case it is a value)"
            )
        object.__setattr__(self, "ref", ref)

    def __setattr__(self, name: str, value: Any) -> None:
        raise AttributeError("a Secret is immutable")

    @property
    def name(self) -> str:
        """The reference, as reports show it."""
        return self.ref

    def value(self, resolver: Resolver | None = None) -> str:
        """The value now.

        Args:
            resolver: Where to look. Default: the installed one.

        Returns:
            The value, as a string.

        Raises:
            SecretError: The secret cannot be read, or it has several
                fields and the reference picks none.
        """
        return (resolver or current()).value(self)

    def fields(self, resolver: Resolver | None = None) -> dict[str, str]:
        """The secret's fields now, for a secret that holds several (a KV
        entry, a JSON object, `env:PREFIX_*`).

        Raises:
            SecretError: The secret cannot be read, or holds one value.
        """
        return (resolver or current()).fields(self)

    def __repr__(self) -> str:
        return f"Secret({self.ref!r})"

    def __str__(self) -> str:
        return self.ref

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Secret) and other.ref == self.ref

    def __hash__(self) -> int:
        return hash(("Secret", self.ref))

    def __reduce__(self) -> tuple[Any, ...]:
        return (Secret, (self.ref,))


def _reference(ref: str) -> tuple[str, str, str | None] | None:
    """`(scheme, path, field)` of a reference, or None for none."""
    m = _SCHEME.fullmatch(ref)
    if m is None or m.group(1) not in _SCHEMES:
        return None
    path, _, field = m.group(2).partition("#")
    if not path or any(c.isspace() for c in ref):
        return None
    return m.group(1), path, field or None


def as_secret(value: str | Secret | None, what: str) -> Secret | None:
    """A secret argument: None, a `Secret`, or a name or reference."""
    if value is None or isinstance(value, Secret):
        return value
    if not isinstance(value, str):
        raise TypeError(f"{what} takes a secret's name or a Secret, got {type(value).__name__}")
    return Secret(value)


def _fail(ref: str, what: str) -> SecretError:
    return SecretError(f"secret {ref!r}: {what}")


def _parse_fields(text: str) -> dict[str, str] | None:
    """Fields of a text: a JSON object, or `KEY=value` lines."""
    s = text.strip()
    if s.startswith("{"):
        try:
            got = json.loads(s)
        except ValueError:
            return None
        if isinstance(got, dict):
            return {str(k): str(v) for k, v in got.items()}
        return None
    lines = [ln for ln in s.splitlines() if ln.strip() and not ln.lstrip().startswith("#")]
    if lines and all("=" in ln for ln in lines):
        out = {}
        for ln in lines:
            k, _, v = ln.partition("=")
            out[k.strip().removeprefix("export ").strip()] = v.strip().strip("'\"")
        return out
    return None


# -- backends ----------------------------------------------------------------


class Env:
    """Environment variables: `env:NAME`, or `env:PREFIX_*` for fields."""

    def __init__(self, environ: Mapping[str, str] | None = None):
        self.environ = environ

    def get(self, path: str) -> Value:
        env = os.environ if self.environ is None else self.environ
        if path.endswith("*"):
            prefix = path[:-1]
            got = {k[len(prefix) :]: v for k, v in env.items() if k.startswith(prefix)}
            if not got:
                raise KeyError("no variable has that prefix")
            return got
        return env[path]


class File:
    """Files: `file:/path`; `~` is the home directory."""

    def get(self, path: str) -> Value:
        return Path(path).expanduser().read_text().rstrip("\n")


def _github_oidc(audience: str) -> str:
    """A GitHub Actions OIDC token for `audience` (the job needs
    `permissions: id-token: write`)."""
    import urllib.parse
    import urllib.request

    url = os.environ.get("ACTIONS_ID_TOKEN_REQUEST_URL")
    bearer = os.environ.get("ACTIONS_ID_TOKEN_REQUEST_TOKEN")
    if not url or not bearer:
        raise Refused("no GitHub Actions OIDC token: the job needs `permissions: id-token: write`")
    sep = "&" if "?" in url else "?"
    req = urllib.request.Request(  # noqa: S310 - GitHub's own URL
        f"{url}{sep}audience={urllib.parse.quote(audience)}",
        headers={"Authorization": f"Bearer {bearer}"},
    )
    with urllib.request.urlopen(req, timeout=10) as resp:  # noqa: S310
        return json.loads(resp.read())["value"]


class Bao:
    """OpenBao's or Vault's KV store over HTTP: `bao:<mount>/<path>`.

    Its address is `address`, else `BAO_ADDR`, else `VAULT_ADDR`. It logs
    in with `auth`:

    * `"token"` (the default): `BAO_TOKEN` or `VAULT_TOKEN`, else the file
      `token_file` (default `~/.vault-token`, where `bao login` and an
      agent's sink put it);
    * `"jwt"`: the JWT auth method at `jwt_mount` with `role`, logging in
      with the GitHub Actions OIDC token for `audience` (#776), or the
      token in `jwt_file`. Nothing is stored: the login lasts as long as
      the role's TTL, and is kept in memory for that long.

    Args:
        address: The server, such as `https://bao.example.ts.net:8200`.
        auth: `"token"` or `"jwt"`.
        role: The JWT role.
        audience: The OIDC token's audience. Default "openbao".
        jwt_mount: Where the JWT method is enabled. Default "jwt".
        jwt_file: A file holding the JWT, for runners other than GitHub's.
        token_file: The token's file for `auth="token"`.
        kv_version: 2 (the default) or 1.
        namespace: The namespace header (Vault Enterprise, OpenBao).
        ca_cert: A CA bundle to verify the server with.
        timeout: Seconds a request may take. Default 10.
    """

    def __init__(
        self,
        address: str | None = None,
        *,
        auth: str = "token",
        role: str | None = None,
        audience: str = "openbao",
        jwt_mount: str = "jwt",
        jwt_file: str | None = None,
        token_file: str | None = None,
        kv_version: int = 2,
        namespace: str | None = None,
        ca_cert: str | None = None,
        timeout: float = 10.0,
        env_prefix: str = "BAO",
    ):
        if auth not in ("token", "jwt"):
            raise ValueError(f"auth is 'token' or 'jwt', got {auth!r}")
        if auth == "jwt" and not role:
            raise ValueError("auth='jwt' needs a role")
        self.address, self.auth, self.role = address, auth, role
        self.audience, self.jwt_mount, self.jwt_file = audience, jwt_mount, jwt_file
        self.token_file, self.kv_version, self.namespace = token_file, kv_version, namespace
        self.ca_cert, self.timeout, self.env_prefix = ca_cert, timeout, env_prefix
        self._login: tuple[str, float] | None = None
        self._lock = threading.Lock()

    def __repr__(self) -> str:
        return f"Bao({self.address or '$' + self.env_prefix + '_ADDR'}, auth={self.auth!r})"

    def _addr(self) -> str:
        addr = (
            self.address
            or os.environ.get(f"{self.env_prefix}_ADDR")
            or os.environ.get("VAULT_ADDR")
        )
        if not addr:
            raise Refused(f"no address: set {self.env_prefix}_ADDR or the backend's address")
        return addr.rstrip("/")

    def _request(self, path: str, token: str | None, body: Any = None) -> Any:
        import ssl
        import urllib.error
        import urllib.request

        headers = {"Content-Type": "application/json"}
        if token:
            headers["X-Vault-Token"] = token
        if self.namespace:
            headers["X-Vault-Namespace"] = self.namespace
        req = urllib.request.Request(  # noqa: S310 - the configured server
            f"{self._addr()}/v1/{path}",
            data=None if body is None else json.dumps(body).encode(),
            headers=headers,
            method="GET" if body is None else "POST",
        )
        ctx = ssl.create_default_context(cafile=self.ca_cert) if self.ca_cert else None
        try:
            with urllib.request.urlopen(req, timeout=self.timeout, context=ctx) as resp:  # noqa: S310
                return json.loads(resp.read())
        except urllib.error.HTTPError as e:
            code = e.code
        # Outside the handler: the server's body may echo what it was sent.
        raise Refused(f"the server answered HTTP {code}")

    def _token(self) -> str:
        if self.auth == "token":
            tok = os.environ.get(f"{self.env_prefix}_TOKEN") or os.environ.get("VAULT_TOKEN")
            if tok:
                return tok
            return Path(self.token_file or "~/.vault-token").expanduser().read_text().strip()
        with self._lock:
            if self._login is not None and self._login[1] > time.monotonic():
                return self._login[0]
            jwt = (
                Path(self.jwt_file).expanduser().read_text().strip()
                if self.jwt_file
                else _github_oidc(self.audience)
            )
            got = self._request(
                f"auth/{self.jwt_mount}/login", None, {"role": self.role, "jwt": jwt}
            )["auth"]
            # Renew a minute before the lease ends.
            self._login = (
                got["client_token"],
                time.monotonic() + max(0, got["lease_duration"] - 60),
            )
            return self._login[0]

    def get(self, path: str) -> Value:
        mount, _, rest = path.partition("/")
        if not rest:
            raise Refused("a path is <mount>/<path>")
        if self.kv_version == 2:
            data = self._request(f"{mount}/data/{rest}", self._token())["data"]["data"]
        else:
            data = self._request(f"{mount}/{rest}", self._token())["data"]
        return {str(k): str(v) for k, v in data.items()}


class AwsSecretsManager:
    """AWS Secrets Manager: `aws-sm:<secret id or ARN>`, with boto3's
    default credentials (`pip install 'sverify[secrets-aws]'`)."""

    def __init__(self, region: str | None = None):
        self.region = region

    def get(self, path: str) -> Value:
        import boto3  # pyrefly: ignore

        client = boto3.client("secretsmanager", region_name=self.region)
        return client.get_secret_value(SecretId=path)["SecretString"]


class GcpSecretManager:
    """Google Secret Manager: `gcp-sm:projects/<p>/secrets/<s>[/versions/<v>]`,
    with the default credentials (`pip install 'sverify[secrets-gcp]'`)."""

    def get(self, path: str) -> Value:
        from google.cloud import secretmanager  # pyrefly: ignore

        name = path if "/versions/" in path else f"{path}/versions/latest"
        got = secretmanager.SecretManagerServiceClient().access_secret_version(name=name)
        return got.payload.data.decode()


class AzureKeyVault:
    """Azure Key Vault: `azure-kv:<vault>/<secret>`, with
    `DefaultAzureCredential` (`pip install 'sverify[secrets-azure]'`)."""

    def get(self, path: str) -> Value:
        from azure.identity import DefaultAzureCredential  # pyrefly: ignore
        from azure.keyvault.secrets import SecretClient  # pyrefly: ignore

        vault, _, name = path.partition("/")
        if not name:
            raise Refused("a path is <vault>/<secret>")
        url = vault if vault.startswith("https://") else f"https://{vault}.vault.azure.net"
        return SecretClient(url, DefaultAzureCredential()).get_secret(name).value or ""


class Keychain:
    """The OS keychain (macOS Keychain, Secret Service, Windows Credential
    Locker): `keychain:<service>/<account>` (`pip install
    'sverify[secrets-keychain]'`)."""

    def get(self, path: str) -> Value:
        import keyring  # pyrefly: ignore

        service, _, account = path.rpartition("/")
        got = keyring.get_password(service, account)
        if got is None:
            raise KeyError("no such entry")
        return got


_SCHEMES: dict[str, Callable[[Mapping[str, Any]], Backend]] = {
    "env": lambda c: Env(),
    "file": lambda c: File(),
    "bao": lambda c: Bao(**c),  # pyrefly: ignore
    "vault": lambda c: Bao(**{"env_prefix": "VAULT", **c}),  # pyrefly: ignore
    "aws-sm": lambda c: AwsSecretsManager(**c),
    "gcp-sm": lambda c: GcpSecretManager(**c),
    "azure-kv": lambda c: AzureKeyVault(**c),
    "keychain": lambda c: Keychain(**c),
}
_EXTRA = {
    "aws-sm": "secrets-aws",
    "gcp-sm": "secrets-gcp",
    "azure-kv": "secrets-azure",
    "keychain": "secrets-keychain",
}


# -- the resolver ------------------------------------------------------------


class Resolver:
    """Looks secrets up: which backend reads each scheme, what each bare
    name stands for, and the scope of each credential (#778).

    The default resolver comes from configuration: the TOML file
    `SVERIFY_SECRETS` names, else the `[tool.sverify.secrets]` table of the
    nearest `pyproject.toml` (from the working directory up), else none.

    ```toml
    [tool.sverify.secrets]
    default = "env"            # the backend that reads bare names

    [tool.sverify.secrets.bao]  # options of a backend, by scheme
    address = "https://bao.example.ts.net:8200"
    auth = "jwt"
    role = "pipelines-production"

    [tool.sverify.secrets.names]
    eurostat = "env:EUROSTAT_TOKEN"
    lake = { ref = "bao:kv/pipelines/production", writes = ["s3://lake/production/"] }
    ```

    A name's `reads` and `writes` are the URI prefixes its credential may
    read and write; `Storage(credentials=name)` takes them, and `sverify
    check` warns about a source or sink outside them.

    Remote backends' answers are kept for `cache_seconds` (default 60), so
    a refresh that opens many tables asks once; environment variables and
    files are read every time.

    Args:
        names: Bare names, mapped to references or to tables with `ref`,
            `reads` and `writes`.
        default: The scheme that reads bare names not in `names`. Default
            "env".
        backends: Backends by scheme: options for a built-in one, or an
            object with `get(path)`.
        cache_seconds: How long remote answers are kept. 0 keeps none.
    """

    def __init__(
        self,
        names: Mapping[str, Any] | None = None,
        *,
        default: str = "env",
        backends: Mapping[str, Any] | None = None,
        cache_seconds: float = 60.0,
    ):
        if default not in _SCHEMES and default not in (backends or {}):
            raise ValueError(f"default: no backend {default!r}; there are {sorted(_SCHEMES)}")
        self.default = default
        self.cache_seconds = cache_seconds
        self._names: dict[str, str] = {}
        self._scopes: dict[str, tuple[tuple[str, ...], tuple[str, ...]]] = {}
        for name, entry in (names or {}).items():
            if isinstance(entry, Mapping):
                ref = entry["ref"]
                self._scopes[name] = (
                    tuple(entry.get("reads", ())),
                    tuple(entry.get("writes", ())),
                )
            else:
                ref = entry
            if _reference(str(ref)) is None:
                raise ValueError(f"names.{name}: {ref!r} is not a reference (scheme:path)")
            self._names[name] = str(ref)
        self._options: dict[str, Mapping[str, Any]] = {}
        self._backends: dict[str, Backend] = {}
        for scheme, b in (backends or {}).items():
            if hasattr(b, "get") and not isinstance(b, Mapping):
                self._backends[scheme] = b
            else:
                self._options[scheme] = dict(b)
        self._cache: dict[str, tuple[float, Value]] = {}
        self._lock = threading.Lock()

    @classmethod
    def from_config(cls, path: str | Path | None = None) -> Resolver:
        """The resolver a configuration file describes.

        Args:
            path: A TOML file: its `[tool.sverify.secrets]` table, or the
                whole file if it has none. Default: `SVERIFY_SECRETS`, else
                the nearest `pyproject.toml`, else no configuration.
        """
        import tomllib

        table: Mapping[str, Any] = {}
        file = Path(path) if path else _config_file()
        if file is not None:
            data = tomllib.loads(file.read_text())
            nested = data.get("tool", {}).get("sverify", {}).get("secrets")
            table = nested if nested is not None or file.name == "pyproject.toml" else data
            table = table or {}
        table = dict(table)
        names = table.pop("names", {})
        default = table.pop("default", "env")
        cache = table.pop("cache_seconds", 60.0)
        return cls(names, default=default, backends=table, cache_seconds=cache)

    def __repr__(self) -> str:
        return f"Resolver(names={sorted(self._names)}, default={self.default!r})"

    def reference(self, secret: Secret | str) -> str:
        """The reference a secret or name stands for."""
        ref = Secret(secret).ref
        if _reference(ref) is not None:
            return ref
        if ref in self._names:
            return self._names[ref]
        if self.default == "env":
            return "env:" + re.sub(r"[^A-Za-z0-9_]", "_", ref).upper()
        return f"{self.default}:{ref}"

    def scope(self, secret: Secret | str) -> tuple[tuple[str, ...], tuple[str, ...]]:
        """The prefixes a named credential may read and write, as configured
        (empty when unknown)."""
        return self._scopes.get(Secret(secret).ref, ((), ()))

    def _backend(self, scheme: str) -> Backend:
        if scheme not in self._backends:
            try:
                self._backends[scheme] = _SCHEMES[scheme](self._options.get(scheme, {}))
            except TypeError as e:
                bad = str(e)
                raise ValueError(f"[secrets.{scheme}]: {bad}") from None
        return self._backends[scheme]

    def _lookup(self, secret: Secret | str) -> tuple[str, Value, str | None]:
        """The reference, what its backend returned, and the field asked for."""
        name = Secret(secret).ref
        ref = self.reference(name)
        parsed = _reference(ref)
        if parsed is None:  # a scheme of a backend given in `backends`
            scheme, _, rest = ref.partition(":")
            path, _, field = rest.partition("#")
            parsed = (scheme, path, field or None)
        scheme, path, field = parsed
        key = f"{scheme}:{path}"
        remote = scheme not in ("env", "file")
        now = time.monotonic()
        if remote and self.cache_seconds > 0:
            with self._lock:
                hit = self._cache.get(key)
            if hit is not None and hit[0] > now:
                return ref, hit[1], field
        problem: str | None = None
        got: Value = ""
        try:
            got = self._backend(scheme).get(path)
        except ImportError:
            extra = _EXTRA.get(scheme)
            problem = "its backend is not installed" + (
                f": pip install 'sverify[{extra}]'" if extra else ""
            )
        except Refused as e:
            problem = str(e)
        except (KeyError, FileNotFoundError):
            problem = "not found" + (f" (it stands for {ref!r})" if ref != name else "")
        except Exception as e:  # noqa: BLE001 - a backend's error may carry values
            problem = f"its backend failed ({type(e).__name__})"
        if problem is not None:
            # Raised here, outside the handler, so no `__context__` keeps the
            # backend's own exception, whose text may hold a value.
            raise _fail(name, problem)
        if remote and self.cache_seconds > 0:
            with self._lock:
                self._cache[key] = (now + self.cache_seconds, got)
        return ref, got, field

    def value(self, secret: Secret | str) -> str:
        """The value of a secret now (see `Secret.value`)."""
        ref, got, field = self._lookup(secret)
        if isinstance(got, str) and field is not None:
            got = _parse_fields(got) or {}
        if isinstance(got, Mapping):
            if field is None:
                if len(got) == 1:
                    return next(iter(got.values()))
                raise _fail(str(secret), f"it has fields {sorted(got)}; pick one with '#<field>'")
            if field not in got:
                raise _fail(str(secret), f"no field {field!r}; it has {sorted(got)}")
            return got[field]
        return got

    def fields(self, secret: Secret | str) -> dict[str, str]:
        """The fields of a secret now (see `Secret.fields`)."""
        ref, got, field = self._lookup(secret)
        if field is not None:
            return {field: self.value(secret)}
        if isinstance(got, str):
            parsed = _parse_fields(got)
            if parsed is None:
                raise _fail(str(secret), "it holds one value, not fields")
            got = parsed
        return dict(got)

    def clear(self) -> None:
        """Forget the remote answers kept."""
        with self._lock:
            self._cache.clear()


def _config_file() -> Path | None:
    env = os.environ.get("SVERIFY_SECRETS")
    if env:
        return Path(env).expanduser()
    here = Path.cwd()
    for d in (here, *here.parents):
        p = d / "pyproject.toml"
        if p.is_file():
            return p
    return None


_current: Resolver | None = None


def current() -> Resolver:
    """The installed resolver: `set_resolver`'s, else the configuration's,
    read once."""
    global _current
    if _current is None:
        _current = Resolver.from_config()
    return _current


def set_resolver(resolver: Resolver | None) -> None:
    """Install the resolver every `Secret` reads through; None goes back to
    the configuration's (read again on next use).

    Args:
        resolver: The resolver, or None.
    """
    global _current
    _current = resolver


def resolve_values(options: Mapping[str, Any]) -> dict[str, str]:
    """A mapping with each `Secret` value replaced by its value now."""
    return {k: v.value() if isinstance(v, Secret) else v for k, v in options.items()}

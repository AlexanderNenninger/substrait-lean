"""What an AWS session may touch, from the identity's own IAM policies (#778).

Internal: not part of sverify's public API (`docs/stability.md`).

`aws_scope(options)` asks STS who the session is (`GetCallerIdentity`), reads
the policies attached to that role or user, and turns their plain `Allow`
statements on S3 objects into URI prefixes. It answers only when it can state
the scope without guessing: a `Deny`, a `NotAction` or `NotResource`, a
`Condition`, or a resource pattern that is not a prefix leaves it unknown
(None), as does a missing `boto3`, a denied IAM read or any error. A session
policy, a permissions boundary and a bucket policy are not in the identity's
policies, so the prefixes are what its policies grant, not a promise of what
the store allows.
"""

from __future__ import annotations

import json
import re
from collections.abc import Mapping
from fnmatch import fnmatchcase
from typing import Any

Scope = tuple[tuple[str, ...], tuple[str, ...]]

_CACHE: dict[tuple[str, str], Scope | None] = {}
"""The scope per access key and endpoint: one lookup per credential and process."""


def aws_scope(options: Mapping[str, str]) -> Scope | None:
    """The prefixes the session in `options` may read and write, or None.

    Args:
        options: Storage options with `AWS_ACCESS_KEY_ID`,
            `AWS_SECRET_ACCESS_KEY`, and optionally `AWS_SESSION_TOKEN`,
            `AWS_REGION` and `AWS_ENDPOINT_URL`.
    """
    key = options.get("AWS_ACCESS_KEY_ID")
    secret = options.get("AWS_SECRET_ACCESS_KEY")
    if not key or not secret:
        return None
    endpoint = options.get("AWS_ENDPOINT_URL", "")
    if (key, endpoint) not in _CACHE:
        _CACHE[key, endpoint] = _lookup(options, key, secret, endpoint)
    return _CACHE[key, endpoint]


def _lookup(options: Mapping[str, str], key: str, secret: str, endpoint: str) -> Scope | None:
    try:
        import boto3  # pyrefly: ignore
    except ImportError:
        return None
    try:
        kw: dict[str, Any] = {
            "aws_access_key_id": key,
            "aws_secret_access_key": secret,
            "aws_session_token": options.get("AWS_SESSION_TOKEN"),
            "region_name": options.get("AWS_REGION") or "us-east-1",
        }
        if endpoint:
            kw["endpoint_url"] = endpoint
        from botocore.config import Config  # pyrefly: ignore

        # An offline or firewalled check must not stall on boto3's defaults.
        kw["config"] = Config(
            connect_timeout=3, read_timeout=5, retries={"max_attempts": 1, "mode": "standard"}
        )
        arn = boto3.client("sts", **kw).get_caller_identity()["Arn"]
        docs = _policies(boto3.client("iam", **kw), arn)
    except Exception:  # noqa: BLE001 - any failure means the store reports nothing
        return None
    return None if docs is None else _prefixes(docs)


def _policies(iam: Any, arn: str) -> list[dict[str, Any]] | None:
    """The policy documents attached to the role or user `arn` names."""
    m = re.fullmatch(r"arn:aws[\w-]*:(?:sts|iam)::\d+:(assumed-role|role|user)/(.+)", arn)
    if m is None:
        return None
    kind, path = m[1], m[2].split("/")
    name = path[0] if kind == "assumed-role" else path[-1]  # assumed-role/NAME/SESSION
    if kind == "user":
        groups = [g["GroupName"] for g in iam.list_groups_for_user(UserName=name)["Groups"]]
        return _documents(iam, "User", name) + [
            d for g in groups for d in _documents(iam, "Group", g)
        ]
    return _documents(iam, "Role", name)


def _documents(iam: Any, kind: str, name: str) -> list[dict[str, Any]]:
    """The attached and inline policy documents of a role, user or group."""
    ident = {f"{kind}Name": name}
    docs = []
    for p in getattr(iam, f"list_attached_{kind.lower()}_policies")(**ident)["AttachedPolicies"]:
        arn = p["PolicyArn"]
        version = iam.get_policy(PolicyArn=arn)["Policy"]["DefaultVersionId"]
        docs.append(
            iam.get_policy_version(PolicyArn=arn, VersionId=version)["PolicyVersion"]["Document"]
        )
    for n in getattr(iam, f"list_{kind.lower()}_policies")(**ident)["PolicyNames"]:
        got = getattr(iam, f"get_{kind.lower()}_policy")(**ident, PolicyName=n)
        docs.append(got["PolicyDocument"])
    return [json.loads(d) if isinstance(d, str) else d for d in docs]


def _prefixes(docs: list[dict[str, Any]]) -> Scope | None:
    reads: list[str] = []
    writes: list[str] = []
    for doc in docs:
        statements = doc.get("Statement", [])
        for s in [statements] if isinstance(statements, dict) else statements:
            if "NotAction" in s or "NotResource" in s:
                return None
            actions = [a.lower().removeprefix("s3:") for a in _as_list(s.get("Action"))]
            actions = [a for a in actions if ":" not in a]  # other services' actions
            read = any(fnmatchcase("getobject", a) for a in actions)
            write = any(fnmatchcase("putobject", a) for a in actions)
            if not (read or write):
                continue  # ListBucket and the like grant no object access
            if s.get("Effect") != "Allow" or "Condition" in s:
                return None  # a Deny or a condition: not a plain grant
            uris = [_uri(r) for r in _as_list(s.get("Resource"))]
            if None in uris:
                return None
            found = [u for u in uris if u]  # "" is a bucket itself: no object access
            reads += found if read else []
            writes += found if write else []
    return tuple(dict.fromkeys(reads)), tuple(dict.fromkeys(writes))


def _as_list(v: Any) -> list[Any]:
    return [] if v is None else v if isinstance(v, list) else [v]


def _uri(resource: str) -> str | None:
    """`arn:aws:s3:::bucket/prefix/*` as `s3://bucket/prefix/`; "" for a
    bucket's own ARN, which grants no object access; None for a pattern that
    is not a prefix (a `*` or `?` inside it)."""
    if resource == "*":
        return "s3://"
    if re.fullmatch(r"arn:aws[\w-]*:s3:::[^/*?]+", resource):
        return ""
    m = re.fullmatch(r"arn:aws[\w-]*:s3:::([^/*?]+)/([^*?]*)\*?", resource)
    return None if m is None else f"s3://{m[1]}/{m[2]}"

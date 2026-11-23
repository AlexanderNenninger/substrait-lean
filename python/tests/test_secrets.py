"""Secrets by name and the resolver (#775). Every value here is a test value."""

from __future__ import annotations

import json
import pickle
import sys
import threading
from http.server import BaseHTTPRequestHandler, HTTPServer

import pytest

from sverify.errors import SecretError
from sverify.io import Resolver, Secret, Storage, set_resolver
from sverify.io._secrets import Bao

VALUE = "sv-test-value-0d4f"


@pytest.fixture(autouse=True)
def _fresh():
    set_resolver(Resolver())
    yield
    set_resolver(None)


def test_a_secret_shows_its_reference_only(monkeypatch):
    monkeypatch.setenv("SV_TEST_TOKEN", VALUE)
    s = Secret("env:SV_TEST_TOKEN")
    assert s.value() == VALUE
    assert VALUE not in repr(s) + str(s) + repr(pickle.loads(pickle.dumps(s)))
    assert pickle.loads(pickle.dumps(s)) == s
    assert VALUE not in pickle.dumps(s).decode("latin-1")
    with pytest.raises(AttributeError):
        s.ref = "env:OTHER"  # type: ignore[misc]


@pytest.mark.parametrize("bad", ["has space value", "", "x" * 200, "notascheme:/x y"])
def test_a_value_given_by_mistake_is_not_repeated(bad):
    with pytest.raises(SecretError) as e:
        Secret(bad)
    assert bad not in str(e.value) or not bad


def test_bare_names_read_the_environment(monkeypatch):
    monkeypatch.setenv("FLIGHT_TOKEN", VALUE)
    assert Secret("flight-token").value() == VALUE
    assert Resolver().reference("flight-token") == "env:FLIGHT_TOKEN"


def test_names_map_to_references(monkeypatch, tmp_path):
    monkeypatch.setenv("EUROSTAT_KEY", VALUE)
    (tmp_path / "pyproject.toml").write_text(
        """
[tool.sverify.secrets.names]
eurostat = "env:EUROSTAT_KEY"
lake = { ref = "env:LAKE_*", writes = ["s3://lake/marts/"] }
"""
    )
    r = Resolver.from_config(tmp_path / "pyproject.toml")
    assert r.value("eurostat") == VALUE
    assert r.scope("lake") == ((), ("s3://lake/marts/",))
    monkeypatch.setenv("SVERIFY_SECRETS", str(tmp_path / "pyproject.toml"))
    set_resolver(None)
    assert Secret("eurostat").value() == VALUE


def test_env_prefix_gives_fields(monkeypatch):
    monkeypatch.setenv("LAKE_AWS_ACCESS_KEY_ID", "sv-test-id")
    monkeypatch.setenv("LAKE_AWS_SECRET_ACCESS_KEY", VALUE)
    assert Secret("env:LAKE_*").fields() == {
        "AWS_ACCESS_KEY_ID": "sv-test-id",
        "AWS_SECRET_ACCESS_KEY": VALUE,
    }
    assert Secret("env:LAKE_*#AWS_SECRET_ACCESS_KEY").value() == VALUE
    with pytest.raises(SecretError, match="pick one") as e:
        Secret("env:LAKE_*").value()
    assert VALUE not in str(e.value)


def test_files_hold_a_value_json_or_lines(tmp_path):
    (tmp_path / "token").write_text(VALUE + "\n")
    (tmp_path / "lake.json").write_text(json.dumps({"key": VALUE, "id": "x"}))
    (tmp_path / "lake.env").write_text(f"# test\nexport KEY='{VALUE}'\nID=x\n")
    assert Secret(f"file:{tmp_path}/token").value() == VALUE
    assert Secret(f"file:{tmp_path}/lake.json#key").value() == VALUE
    assert Secret(f"file:{tmp_path}/lake.env").fields() == {"KEY": VALUE, "ID": "x"}
    # Without a field, a file is its text.
    assert json.loads(Secret(f"file:{tmp_path}/lake.json").value())["id"] == "x"


def test_errors_name_the_reference_and_carry_no_value(monkeypatch, tmp_path):
    with pytest.raises(SecretError, match="SV_MISSING.*not found") as e:
        Secret("env:SV_MISSING").value()
    assert e.value.__context__ is None and e.value.__cause__ is None

    class Leaky:
        def get(self, path):
            raise RuntimeError(f"backend echoed {VALUE}")

    r = Resolver(backends={"leaky": Leaky()}, default="leaky")
    with pytest.raises(SecretError) as e:
        r.value("anything")
    assert VALUE not in str(e.value)
    assert e.value.__context__ is None and e.value.__cause__ is None
    assert "RuntimeError" in str(e.value)


def test_a_missing_backend_names_its_extra(monkeypatch):
    import builtins

    real = builtins.__import__

    def no_boto(name, *a, **k):
        if name == "boto3":
            raise ImportError(name)
        return real(name, *a, **k)

    monkeypatch.setattr(builtins, "__import__", no_boto)
    with pytest.raises(SecretError, match=r"sverify\[secrets-aws\]"):
        Secret("aws-sm:prod/lake").value()


def test_storage_resolves_when_a_table_opens(monkeypatch):
    monkeypatch.setenv("LAKE_AWS_SECRET_ACCESS_KEY", VALUE)
    monkeypatch.setenv("SV_KEY", VALUE)
    s = Storage(credentials="env:LAKE_*", writes=["s3://lake/marts"])
    assert s.options() == {"AWS_SECRET_ACCESS_KEY": VALUE}
    t = Storage({"AWS_REGION": "eu-central-1", "AWS_SECRET_ACCESS_KEY": Secret("env:SV_KEY")})
    assert t.options()["AWS_SECRET_ACCESS_KEY"] == VALUE
    assert VALUE not in repr(s) + repr(t) + s.label + t.label
    assert t.label == "env:SV_KEY" and s.writes == ("s3://lake/marts",)
    assert Storage().label == "default chain"


class _Bao(BaseHTTPRequestHandler):
    """A KV v2 store and a JWT login, as OpenBao answers them."""

    calls: list[str] = []
    namespaces: list[str | None] = []

    def log_message(self, format, *args):  # noqa: A002 - the parent's name
        pass

    def _send(self, code, body):
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(body).encode())

    def do_GET(self):
        _Bao.calls.append(self.path)
        _Bao.namespaces.append(self.headers.get("X-Vault-Namespace"))
        if self.path.startswith("/oidc?"):
            # GitHub's OIDC token endpoint.
            if self.headers.get("Authorization") != "Bearer sv-test-request-token":
                return self._send(403, {})
            return self._send(200, {"value": "sv-test-jwt"})
        if self.headers.get("X-Vault-Token") != "sv-test-bao-token":
            return self._send(403, {"errors": [f"permission denied {VALUE}"]})
        if self.path == "/v1/kv/data/pipelines/lake":
            return self._send(200, {"data": {"data": {"access_key": "id", "secret_key": VALUE}}})
        if self.path == "/v1/kv1/pipelines/lake":
            return self._send(200, {"data": {"secret_key": VALUE, "port": 5432, "tls": True}})
        return self._send(404, {"errors": []})

    def do_POST(self):
        _Bao.calls.append("POST " + self.path)
        body = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
        if self.path == "/v1/auth/jwt/login" and body == {"role": "ci", "jwt": "sv-test-jwt"}:
            return self._send(
                200, {"auth": {"client_token": "sv-test-bao-token", "lease_duration": 900}}
            )
        return self._send(400, {"errors": [f"bad login {body}"]})


@pytest.fixture
def bao():
    server = HTTPServer(("127.0.0.1", 0), _Bao)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    _Bao.calls, _Bao.namespaces = [], []
    yield f"http://127.0.0.1:{server.server_port}"
    server.shutdown()


def test_openbao_with_a_token(bao, monkeypatch):
    monkeypatch.setenv("BAO_TOKEN", "sv-test-bao-token")
    r = Resolver(backends={"bao": {"address": bao}})
    assert r.value("bao:kv/pipelines/lake#secret_key") == VALUE
    assert r.fields("bao:kv/pipelines/lake") == {"access_key": "id", "secret_key": VALUE}
    # Kept for cache_seconds: one request for both.
    assert len(_Bao.calls) == 1
    monkeypatch.setenv("BAO_TOKEN", "sv-test-wrong")
    with pytest.raises(SecretError, match="HTTP 403") as e:
        Resolver(backends={"bao": {"address": bao}}).value("bao:kv/pipelines/lake#secret_key")
    assert VALUE not in str(e.value) and e.value.__context__ is None


def test_openbao_with_a_jwt_login(bao, tmp_path, monkeypatch):
    monkeypatch.delenv("BAO_TOKEN", raising=False)
    (tmp_path / "jwt").write_text("sv-test-jwt")
    b = Bao(bao, auth="jwt", role="ci", jwt_file=str(tmp_path / "jwt"))
    assert VALUE not in repr(b)
    r = Resolver(backends={"bao": b}, cache_seconds=0)
    assert r.value("bao:kv/pipelines/lake#secret_key") == VALUE
    assert r.value("bao:kv/pipelines/lake#access_key") == "id"


def test_github_oidc_needs_id_token_permission(bao, monkeypatch):
    monkeypatch.delenv("ACTIONS_ID_TOKEN_REQUEST_URL", raising=False)
    r = Resolver(backends={"bao": {"address": bao, "auth": "jwt", "role": "ci"}})
    with pytest.raises(SecretError, match="kv/pipelines/lake"):
        r.value("bao:kv/pipelines/lake#secret_key")


def test_each_node_lists_its_credentials(tmp_path, monkeypatch):
    """#778: per node, which credential reads or writes which table, and
    whether the table lies inside the credential's scope."""
    pa = pytest.importorskip("pyarrow")
    pytest.importorskip("deltalake")
    from ibis import _

    import sverify as sv
    from sverify.io import CredentialUse, DeltaSink, from_frame

    monkeypatch.setenv("SV_API", VALUE)
    lake = Storage(name="ci-role", writes=[f"{tmp_path}/marts"])
    src = from_frame(
        lambda: pa.table({"id": [1, 2], "x": [1, 20]}), name="api", credentials="sv-api"
    )

    @sv.transform(requires={"t": [_.x >= 0, _.x < 100]})
    def big(t):
        return t.filter(t.x > 10)

    @sv.transform(requires={"t": [_.x >= 0, _.x < 100]}, on_violation="quarantine")
    def big_or_aside(t):
        return t.filter(t.x > 10)

    a = src.pipe(big_or_aside).write(DeltaSink(f"{tmp_path}/marts/a", storage_options=lake))
    b = a.pipe(big).write(DeltaSink(f"{tmp_path}/other/b", storage_options=lake))
    uses = b.credentials()
    got = [(u.table, u.credential, u.access, u.in_scope) for u in uses]
    # `a` may set rows of `api` aside; `b` never does (a's contract proves its
    # preconditions), so its quarantine table is not listed (#1997).
    assert got == [
        ("api", "sv-api", "read", None),
        ("a", "ci-role", "write", True),
        ("a_quarantine", "ci-role", "write", True),
        ("a", "ci-role", "read", True),
        ("b", "ci-role", "write", False),
    ]
    assert uses[0] == CredentialUse("api", "sv-api", "read")
    r = b.refresh()
    assert [u.access for u in r["b"].credentials] == ["read", "write"]
    doc = json.loads(r.to_json())
    assert doc["nodes"][1]["credentials"][1]["in_scope"] is False
    jsonschema = pytest.importorskip("jsonschema")
    from pathlib import Path

    schema = Path(sv.__file__).parent / "schemas" / "refresh.schema.json"
    jsonschema.validate(doc, json.loads(schema.read_text()))
    assert "outside its scope" in str(uses[-1])


def _session(policy: dict):
    """moto: a role with `policy` inline, assumed; its session as Storage options."""
    import boto3

    iam = boto3.client("iam", region_name="us-east-1")
    trust = {
        "Version": "2012-10-17",
        "Statement": [{"Effect": "Allow", "Principal": {"AWS": "*"}, "Action": "sts:AssumeRole"}],
    }
    iam.create_role(RoleName="staging", AssumeRolePolicyDocument=json.dumps(trust))
    iam.put_role_policy(RoleName="staging", PolicyName="p", PolicyDocument=json.dumps(policy))
    got = boto3.client("sts", region_name="us-east-1").assume_role(
        RoleArn="arn:aws:iam::123456789012:role/staging", RoleSessionName="ci"
    )["Credentials"]
    return {
        "AWS_ACCESS_KEY_ID": got["AccessKeyId"],
        "AWS_SECRET_ACCESS_KEY": got["SecretAccessKey"],
        "AWS_SESSION_TOKEN": got["SessionToken"],
    }


def _grant(action, resource, effect="Allow", **extra):
    return {"Effect": effect, "Action": action, "Resource": resource, **extra}


def test_storage_reports_the_scope_of_an_aws_session(monkeypatch):
    """#778: an STS session's scope is read from its role's policies, so a sink
    outside `staging/` is flagged without `writes=`; the lookup is one STS
    call per credential."""
    pytest.importorskip("boto3")
    moto = pytest.importorskip("moto")
    from types import SimpleNamespace

    from sverify.io import _aws_scope
    from sverify.io._credentials import uses

    for k in ("AWS_ACCESS_KEY_ID", "AWS_SECRET_ACCESS_KEY", "AWS_SESSION_TOKEN"):
        monkeypatch.setenv(k, "testing")
    monkeypatch.setattr(_aws_scope, "_CACHE", {})
    calls = []
    real = _aws_scope._lookup
    monkeypatch.setattr(_aws_scope, "_lookup", lambda *a: calls.append(a) or real(*a))
    policy = {
        "Version": "2012-10-17",
        "Statement": [
            _grant(["s3:ListBucket", "s3:GetObject"], ["arn:aws:s3:::lake", "arn:aws:s3:::lake/*"]),
            _grant(["s3:PutObject", "s3:DeleteObject"], "arn:aws:s3:::lake/staging/*"),
        ],
    }
    with moto.mock_aws():
        opts = _session(policy)
        lake = Storage(opts)
        assert lake.reads == ("s3://lake/",) and lake.writes == ("s3://lake/staging/",)
        # declared scope wins; another Storage on the same key asks nothing more
        assert Storage(opts, writes=["s3://lake/x/"]).writes == ("s3://lake/x/",)
        Storage(opts).writes  # noqa: B018
        assert len(calls) == 1
        inside = SimpleNamespace(name="a", uri="s3://lake/staging/a", storage_options=lake)
        outside = SimpleNamespace(name="b", uri="s3://lake/marts/b", storage_options=lake)
        assert uses(inside, "write")[0].in_scope is True
        assert uses(outside, "write")[0].in_scope is False
        assert uses(outside, "read")[0].in_scope is True


@pytest.mark.parametrize(
    "statement",
    [
        _grant("s3:PutObject", "arn:aws:s3:::lake/*", "Deny"),
        _grant("s3:PutObject", "arn:aws:s3:::lake/*", Condition={"StringEquals": {"s3:x": "y"}}),
        _grant("s3:PutObject", "arn:aws:s3:::lake/*/raw/*"),
    ],
)
def test_a_scope_the_policies_do_not_state_plainly_stays_unknown(monkeypatch, statement):
    pytest.importorskip("boto3")
    moto = pytest.importorskip("moto")
    from sverify.io import _aws_scope

    for k in ("AWS_ACCESS_KEY_ID", "AWS_SECRET_ACCESS_KEY", "AWS_SESSION_TOKEN"):
        monkeypatch.setenv(k, "testing")
    monkeypatch.setattr(_aws_scope, "_CACHE", {})
    with moto.mock_aws():
        s = Storage(_session({"Version": "2012-10-17", "Statement": [statement]}))
        assert s.writes is None and s.reads is None


def test_a_users_scope_includes_its_groups_policies(monkeypatch):
    """Most users reach S3 through a group: its grants are part of the scope."""
    boto3 = pytest.importorskip("boto3")
    moto = pytest.importorskip("moto")
    from sverify.io import _aws_scope

    monkeypatch.setattr(_aws_scope, "_CACHE", {})
    with moto.mock_aws():
        iam = boto3.client("iam", region_name="us-east-1")
        iam.create_user(UserName="ci")
        iam.create_group(GroupName="writers")
        iam.add_user_to_group(GroupName="writers", UserName="ci")
        iam.put_user_policy(
            UserName="ci",
            PolicyName="own",
            PolicyDocument=json.dumps(
                {
                    "Version": "2012-10-17",
                    "Statement": [_grant("s3:GetObject", "arn:aws:s3:::lake/*")],
                }
            ),
        )
        iam.put_group_policy(
            GroupName="writers",
            PolicyName="g",
            PolicyDocument=json.dumps(
                {
                    "Version": "2012-10-17",
                    "Statement": [_grant("s3:PutObject", "arn:aws:s3:::lake/marts/*")],
                }
            ),
        )
        key = iam.create_access_key(UserName="ci")["AccessKey"]
        s = Storage(
            {
                "AWS_ACCESS_KEY_ID": key["AccessKeyId"],
                "AWS_SECRET_ACCESS_KEY": key["SecretAccessKey"],
            }
        )
        assert s.reads == ("s3://lake/",) and s.writes == ("s3://lake/marts/",)


# -- references, values and fields ---------------------------------------------


def test_a_secret_is_an_immutable_reference():
    s = Secret("env:SV_KEY")
    assert Secret(s) == s and Secret(s).ref == "env:SV_KEY"
    assert s.name == str(s) == "env:SV_KEY" and repr(s) == "Secret('env:SV_KEY')"
    assert hash(s) == hash(Secret("env:SV_KEY")) and s != "env:SV_KEY"
    assert pickle.loads(pickle.dumps(s)) == s
    with pytest.raises(AttributeError, match="immutable"):
        s.ref = "env:OTHER"  # type: ignore[misc]


@pytest.mark.parametrize("ref", ["env:#field", "env:A B", "nope:path", "1abc", 42])
def test_neither_a_name_nor_a_reference_is_refused(ref):
    with pytest.raises(SecretError, match="neither"):
        Secret(ref)  # type: ignore[arg-type]


def test_a_secret_argument_takes_a_name_or_a_secret():
    from sverify.io._secrets import as_secret

    assert as_secret(None, "credentials") is None
    s = Secret("lake")
    assert as_secret(s, "credentials") is s and as_secret("lake", "credentials") == s
    with pytest.raises(TypeError, match="credentials takes a secret's name or a Secret, got int"):
        as_secret(3, "credentials")  # type: ignore[arg-type]


@pytest.mark.parametrize(
    ("text", "fields"),
    [
        ('{"key": "v"}', {"key": "v"}),
        # #2429: other JSON values are their JSON, not Python's repr.
        (
            '{"port": 5432, "tls": true, "proxy": null, "opts": {"a": 1}}',
            {"port": "5432", "tls": "true", "proxy": "null", "opts": '{"a": 1}'},
        ),
        ('{"key": ', None),
        ('["not", "an", "object"]', None),
        ("KEY=v\n# a comment\n\nexport ID = x", {"KEY": "v", "ID": "x"}),
        ("URL=a=b", {"URL": "a=b"}),
        # #2429: one matching pair of quotes comes off, and no other quote.
        (
            "A='v'\nB=\"v\"\nC=v'\nD=\"v'\nE='\nF=''",
            {
                "A": "v",
                "B": "v",
                "C": "v'",
                "D": "\"v'",
                "E": "'",
                "F": "",
            },
        ),
        ("one value", None),
        ("KEY=v\nno equals sign", None),
    ],
)
def test_the_fields_a_text_holds(text, fields):
    from sverify.io._secrets import _parse_fields

    assert _parse_fields(text) == fields


def test_a_value_with_fields_needs_one_picked(tmp_path, monkeypatch):
    (tmp_path / "two.env").write_text(f"KEY={VALUE}\nID=x\n")
    (tmp_path / "token").write_text(VALUE)
    monkeypatch.setenv("SV_FIELDS_KEY", VALUE)
    monkeypatch.setenv("SV_FIELDS_ID", "x")
    r = Resolver()
    # Several fields need one picked by '#field'.
    assert r.value(f"file:{tmp_path}/two.env#ID") == "x"
    with pytest.raises(SecretError, match=r"it has fields \['ID', 'KEY'\]; pick one") as e:
        r.value("env:SV_FIELDS_*")
    assert VALUE not in str(e.value)
    with pytest.raises(SecretError, match=r"no field 'nope'; it has \['ID', 'KEY'\]") as e:
        r.value(f"file:{tmp_path}/two.env#nope")
    assert VALUE not in str(e.value)
    # A value of one value has no field to pick.
    with pytest.raises(SecretError, match=r"no field 'key'; it has \[\]"):
        r.value(f"file:{tmp_path}/token#key")
    assert r.fields(f"file:{tmp_path}/two.env#KEY") == {"KEY": VALUE}
    with pytest.raises(SecretError, match="it holds one value, not fields") as e:
        r.fields(f"file:{tmp_path}/token")
    assert VALUE not in str(e.value)


def test_a_field_of_one_is_the_value(monkeypatch):
    monkeypatch.setenv("SV_ONE_KEY", VALUE)
    assert Secret("env:SV_ONE_*").value() == VALUE


def test_an_env_prefix_no_variable_has_is_not_found():
    with pytest.raises(SecretError, match="not found"):
        Secret("env:SV_NO_SUCH_PREFIX_*").fields()


def test_a_directory_is_a_backend_failure_naming_its_type(tmp_path):
    with pytest.raises(SecretError, match=r"its backend failed \(IsADirectoryError\)"):
        Secret(f"file:{tmp_path}").value()


# -- the resolver's configuration --------------------------------------------


def test_names_and_defaults_are_checked_when_the_resolver_is_built():
    with pytest.raises(ValueError, match="default: no backend 'nope'"):
        Resolver(default="nope")
    with pytest.raises(ValueError, match="names.lake: 'lake' is not a reference"):
        Resolver(names={"lake": "lake"})
    # #2428: a table without `ref` names what it lacks.
    with pytest.raises(ValueError, match="names.lake: a table names its reference as `ref`"):
        Resolver(names={"lake": {"writes": ["s3://lake/"]}})
    r = Resolver(names={"lake": {"ref": "env:SV_LAKE", "reads": ["s3://a/"]}})
    assert r.scope("lake") == (("s3://a/",), ())
    assert r.scope("other") == ((), ())
    assert repr(r) == "Resolver(names=['lake'], default='env')"


@pytest.mark.parametrize(
    ("options", "error"),
    [
        ({"adress": "http://x"}, r"\[secrets.bao\]: .*unexpected keyword argument 'adress'"),
        ({"auth": "magic"}, "auth is 'token' or 'jwt', got 'magic'"),
        ({"auth": "jwt"}, "auth='jwt' needs a role"),
    ],
)
def test_a_backends_configuration_error_keeps_its_message(options, error):
    # #2428: these became "its backend failed (ValueError)".
    with pytest.raises(SecretError, match=error) as e:
        Resolver(backends={"bao": options}).value("bao:kv/lake#key")
    assert e.value.__context__ is None and e.value.__cause__ is None


def test_a_bare_name_reads_the_default_backend():
    class Kv:
        def get(self, path):
            return {"key": f"{path}-value"}

    r = Resolver(default="kv", backends={"kv": Kv()})
    assert r.reference("lake") == "kv:lake"
    assert r.value("lake") == "lake-value"
    assert Resolver(default="file").reference("token") == "file:token"


def test_the_configuration_file(tmp_path, monkeypatch):
    (tmp_path / "secrets.toml").write_text(
        'default = "file"\ncache_seconds = 0\n[names]\nlake = "env:SV_LAKE"\n'
        '[bao]\naddress = "http://127.0.0.1:1"\n'
    )
    r = Resolver.from_config(tmp_path / "secrets.toml")
    assert (r.default, r.cache_seconds, r.reference("lake")) == ("file", 0, "env:SV_LAKE")
    # A pyproject.toml's own table, found from the working directory up.
    (tmp_path / "pyproject.toml").write_text(
        '[tool.sverify.secrets.names]\nlake = "env:SV_PYPROJECT"\n'
    )
    (tmp_path / "sub").mkdir()
    monkeypatch.chdir(tmp_path / "sub")
    monkeypatch.delenv("SVERIFY_SECRETS", raising=False)
    assert Resolver.from_config().reference("lake") == "env:SV_PYPROJECT"
    # SVERIFY_SECRETS names the file.
    monkeypatch.setenv("SVERIFY_SECRETS", str(tmp_path / "secrets.toml"))
    assert Resolver.from_config().default == "file"
    # A pyproject.toml without the table configures nothing.
    (tmp_path / "pyproject.toml").write_text('[project]\nname = "x"\n')
    monkeypatch.delenv("SVERIFY_SECRETS")
    assert Resolver.from_config().reference("lake") == "env:LAKE"


def test_no_configuration_file_is_the_default_resolver(tmp_path, monkeypatch):
    from sverify.io import _secrets

    monkeypatch.delenv("SVERIFY_SECRETS", raising=False)
    monkeypatch.setattr(_secrets.Path, "cwd", staticmethod(lambda: tmp_path))
    monkeypatch.setattr(_secrets.Path, "is_file", lambda self: False)
    assert _secrets._config_file() is None
    assert Resolver.from_config().reference("lake") == "env:LAKE"


def test_remote_answers_are_kept_until_cleared():
    calls = []

    class Remote:
        def get(self, path):
            calls.append(path)
            return VALUE

    r = Resolver(backends={"bao": Remote()})
    assert r.value("bao:kv/lake") == r.value("bao:kv/lake") == VALUE
    assert calls == ["kv/lake"]
    r.clear()
    r.value("bao:kv/lake")
    assert calls == ["kv/lake", "kv/lake"]


def test_resolve_values_replaces_only_secrets(monkeypatch):
    from sverify.io._secrets import resolve_values

    monkeypatch.setenv("SV_KEY", VALUE)
    assert resolve_values({"key": Secret("env:SV_KEY"), "region": "eu"}) == {
        "key": VALUE,
        "region": "eu",
    }


# -- OpenBao and Vault ------------------------------------------------------------


def test_openbao_without_an_address_names_the_setting(monkeypatch):
    for var in ("BAO_ADDR", "VAULT_ADDR"):
        monkeypatch.delenv(var, raising=False)
    # A token, so the read gets as far as the address, with or without a
    # `~/.vault-token` on this machine.
    for var in ("BAO_TOKEN", "VAULT_TOKEN"):
        monkeypatch.setenv(var, "sv-test-bao-token")
    with pytest.raises(SecretError, match="no address: set `BAO_ADDR`"):
        Secret("bao:kv/lake#key").value()
    with pytest.raises(SecretError, match="no address: set `VAULT_ADDR`"):
        Secret("vault:kv/lake#key").value()
    assert repr(Bao()) == "Bao($BAO_ADDR, auth='token')"


def test_openbao_paths_start_with_the_mount(bao):
    with pytest.raises(SecretError, match="a path is <mount>/<path>"):
        Resolver(backends={"bao": {"address": bao}}).value("bao:kv")


def test_openbao_kv_version_1_and_a_namespace(bao, monkeypatch):
    monkeypatch.setenv("BAO_TOKEN", "sv-test-bao-token")
    r = Resolver(backends={"bao": {"address": bao, "kv_version": 1, "namespace": "team"}})
    # #2429: KV values that are not strings come back as their JSON.
    assert r.fields("bao:kv1/pipelines/lake") == {
        "secret_key": VALUE,
        "port": "5432",
        "tls": "true",
    }
    assert _Bao.calls == ["/v1/kv1/pipelines/lake"] and _Bao.namespaces == ["team"]


def test_openbao_reads_the_token_file(bao, tmp_path, monkeypatch):
    for var in ("BAO_TOKEN", "VAULT_TOKEN"):
        monkeypatch.delenv(var, raising=False)
    (tmp_path / "token").write_text("sv-test-bao-token\n")
    r = Resolver(backends={"bao": {"address": bao, "token_file": str(tmp_path / "token")}})
    assert r.value("bao:kv/pipelines/lake#access_key") == "id"
    missing = Resolver(backends={"bao": {"address": bao, "token_file": str(tmp_path / "none")}})
    with pytest.raises(SecretError, match="not found"):
        missing.value("bao:kv/pipelines/lake#access_key")


def test_a_jwt_login_lasts_its_lease(bao, tmp_path, monkeypatch):
    monkeypatch.delenv("BAO_TOKEN", raising=False)
    (tmp_path / "jwt").write_text("sv-test-jwt")
    b = Bao(bao, auth="jwt", role="ci", jwt_file=str(tmp_path / "jwt"))
    r = Resolver(backends={"bao": b}, cache_seconds=0)
    r.value("bao:kv/pipelines/lake#secret_key")
    r.value("bao:kv/pipelines/lake#access_key")
    assert [c for c in _Bao.calls if c.startswith("POST")] == ["POST /v1/auth/jwt/login"]
    # A minute before the lease ends, it logs in again.
    assert b._login is not None
    b._login = (b._login[0], 0.0)
    r.value("bao:kv/pipelines/lake#access_key")
    assert len([c for c in _Bao.calls if c.startswith("POST")]) == 2
    # A login the server refuses names the status, not what it echoed.
    (tmp_path / "jwt").write_text("sv-test-wrong-jwt")
    b._login = None
    with pytest.raises(SecretError, match="HTTP 400") as e:
        r.value("bao:kv/pipelines/lake#access_key")
    assert "sv-test-wrong-jwt" not in str(e.value)


def test_a_jwt_login_with_the_github_oidc_token(bao, monkeypatch):
    monkeypatch.delenv("BAO_TOKEN", raising=False)
    monkeypatch.setenv("ACTIONS_ID_TOKEN_REQUEST_URL", f"{bao}/oidc?api-version=2.0")
    monkeypatch.setenv("ACTIONS_ID_TOKEN_REQUEST_TOKEN", "sv-test-request-token")
    r = Resolver(backends={"bao": {"address": bao, "auth": "jwt", "role": "ci"}})
    assert r.value("bao:kv/pipelines/lake#secret_key") == VALUE
    assert _Bao.calls[0] == "/oidc?api-version=2.0&audience=openbao"


# -- the cloud backends, with their clients faked ------------------------------------


def _module(monkeypatch, name, **attrs):
    import types

    mod = types.ModuleType(name)
    for k, v in attrs.items():
        setattr(mod, k, v)
    monkeypatch.setitem(sys.modules, name, mod)
    parent, _, child = name.rpartition(".")
    if parent:
        setattr(sys.modules[parent], child, mod)
    return mod


def test_aws_secrets_manager(monkeypatch):
    asked = []

    class Client:
        def get_secret_value(self, SecretId):  # noqa: N803 - boto3's name
            asked.append(SecretId)
            return {"SecretString": json.dumps({"secret_key": VALUE})}

    def client(service, region_name=None):
        asked.append((service, region_name))
        return Client()

    _module(monkeypatch, "boto3", client=client)
    r = Resolver(backends={"aws-sm": {"region": "eu-central-1"}})
    assert r.value("aws-sm:prod/lake#secret_key") == VALUE
    assert asked == [("secretsmanager", "eu-central-1"), "prod/lake"]


def test_gcp_secret_manager_reads_the_latest_version(monkeypatch):
    asked = []

    class Client:
        def access_secret_version(self, name):
            asked.append(name)
            payload = type("P", (), {"data": VALUE.encode()})
            return type("V", (), {"payload": payload})

    _module(monkeypatch, "google")
    _module(monkeypatch, "google.cloud")
    _module(monkeypatch, "google.cloud.secretmanager", SecretManagerServiceClient=Client)
    assert Secret("gcp-sm:projects/p/secrets/lake").value() == VALUE
    assert Secret("gcp-sm:projects/p/secrets/lake/versions/3").value() == VALUE
    assert asked == [
        "projects/p/secrets/lake/versions/latest",
        "projects/p/secrets/lake/versions/3",
    ]


def test_azure_key_vault(monkeypatch):
    asked = []

    class Client:
        def __init__(self, url, credential):
            asked.append(url)

        def get_secret(self, name):
            asked.append(name)
            return type("S", (), {"value": VALUE if name == "lake" else None})

    _module(monkeypatch, "azure")
    _module(monkeypatch, "azure.identity", DefaultAzureCredential=lambda: None)
    _module(monkeypatch, "azure.keyvault")
    _module(monkeypatch, "azure.keyvault.secrets", SecretClient=Client)
    r = Resolver(cache_seconds=0)
    assert r.value("azure-kv:my-vault/lake") == VALUE
    assert r.value("azure-kv:https://vault.example/empty") == ""
    # #2433: a vault's URL, split at the last '/'.
    assert asked == ["https://my-vault.vault.azure.net", "lake", "https://vault.example", "empty"]
    for no_secret in ("my-vault", "https://vault.example"):
        with pytest.raises(SecretError, match="a path is <vault>/<secret>"):
            r.value(f"azure-kv:{no_secret}")


def test_the_os_keychain(monkeypatch):
    def get_password(service, account):
        return VALUE if (service, account) == ("sverify/lake", "ci") else None

    _module(monkeypatch, "keyring", get_password=get_password)
    r = Resolver(cache_seconds=0)
    assert r.value("keychain:sverify/lake/ci") == VALUE
    with pytest.raises(SecretError, match="not found"):
        r.value("keychain:sverify/lake/nobody")


def test_a_field_is_read_with_one_lookup():
    calls = []

    class Counted:
        def get(self, path):
            calls.append(path)
            return {"key": VALUE, "id": "x"}

    r = Resolver(backends={"bao": Counted()}, cache_seconds=0)
    assert r.fields("bao:kv/lake#key") == {"key": VALUE}
    assert calls == ["kv/lake"]


def test_a_backend_of_your_own_serves_bare_names():
    """#2430: a backend under a scheme of its own reads bare names, as the
    `default`. A reference names a built-in scheme only, in a `Secret` and in
    `names` alike."""

    class Kv:
        def get(self, path):
            return {"key": f"{path}-value"}

    r = Resolver(default="kv", backends={"kv": Kv()})
    assert r.value("lake") == "lake-value" and r.reference("lake") == "kv:lake"
    with pytest.raises(SecretError, match="neither"):
        Secret("kv:lake")
    with pytest.raises(ValueError, match="names.lake: 'kv:lake' is not a reference"):
        Resolver(default="kv", backends={"kv": Kv()}, names={"lake": "kv:lake"})

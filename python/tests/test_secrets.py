"""Secrets by name and the resolver (#775). Every value here is a test value."""

from __future__ import annotations

import json
import pickle
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

    def log_message(self, format, *args):  # noqa: A002 - the parent's name
        pass

    def _send(self, code, body):
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(body).encode())

    def do_GET(self):
        _Bao.calls.append(self.path)
        if self.headers.get("X-Vault-Token") != "sv-test-bao-token":
            return self._send(403, {"errors": [f"permission denied {VALUE}"]})
        if self.path == "/v1/kv/data/pipelines/lake":
            return self._send(200, {"data": {"data": {"access_key": "id", "secret_key": VALUE}}})
        return self._send(404, {"errors": []})

    def do_POST(self):
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
    _Bao.calls = []
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

    a = src.pipe(big).write(DeltaSink(f"{tmp_path}/marts/a", storage_options=lake))
    b = a.pipe(big).write(DeltaSink(f"{tmp_path}/other/b", storage_options=lake))
    uses = b.credentials()
    got = [(u.table, u.credential, u.access, u.in_scope) for u in uses]
    assert got == [
        ("api", "sv-api", "read", None),
        ("a", "ci-role", "write", True),
        ("a_quarantine", "ci-role", "write", True),
        ("a", "ci-role", "read", True),
        ("b", "ci-role", "write", False),
        ("b_quarantine", "ci-role", "write", False),
    ]
    assert uses[0] == CredentialUse("api", "sv-api", "read")
    r = b.refresh()
    assert [u.access for u in r["b"].credentials] == ["read", "write", "write"]
    doc = json.loads(r.to_json())
    assert doc["nodes"][1]["credentials"][1]["in_scope"] is False
    jsonschema = pytest.importorskip("jsonschema")
    from pathlib import Path

    schema = Path(sv.__file__).parent / "schemas" / "refresh.schema.json"
    jsonschema.validate(doc, json.loads(schema.read_text()))
    assert "outside its scope" in str(uses[-1])

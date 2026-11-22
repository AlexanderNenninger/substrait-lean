# Credentials

A pipeline names its credentials and holds no value.
The store's default chain comes first: with no options, delta-rs finds
environment variables, `~/.aws` profiles, instance or pod roles, or the
short-lived keys a CI job got through OIDC (the
[pipeline template](../templates/pipelines/docs/for-enterprise.md) does
that). Where a credential has to be fetched, a `sverify.io.Secret` says
where it lives:

| Reference | Where |
|---|---|
| `env:NAME`, `env:PREFIX_*` | environment variables; the prefix form gives fields |
| `file:/run/secrets/lake` | a file: its text, a JSON object, or `KEY=value` lines |
| `bao:kv/pipelines/lake#token` | OpenBao's KV store (`vault:` for Vault) |
| `aws-sm:prod/lake` | AWS Secrets Manager (`sverify[secrets-aws]`) |
| `gcp-sm:projects/p/secrets/lake` | Google Secret Manager (`sverify[secrets-gcp]`) |
| `azure-kv:my-vault/lake` | Azure Key Vault (`sverify[secrets-azure]`) |
| `keychain:service/account` | the OS keychain, for local runs (`sverify[secrets-keychain]`) |

A bare name such as `"lake"` is looked up in `[tool.sverify.secrets]` of the
project's `pyproject.toml`, or in the TOML file `SVERIFY_SECRETS` names;
names it does not list are environment variables (`flight-token` reads
`FLIGHT_TOKEN`). The configuration also says how OpenBao is reached, and
what each credential may read and write:

```toml
[tool.sverify.secrets.bao]
address = "https://bao.example.ts.net:8200"
auth = "jwt"                  # the GitHub Actions OIDC token; "token" reads BAO_TOKEN
role = "pipelines-production"

[tool.sverify.secrets.names]
eurostat = "env:EUROSTAT_TOKEN"
lake = { ref = "bao:kv/pipelines/production", writes = ["s3://lake/production/"] }
```

Sources, sinks and catalogs take the names: `Storage(credentials="lake")`
for a table's object store (the secret's fields are delta-rs options), a
`Secret` as one option's value, `FlightSource(..., secret="flight-token")`,
`Lineage(url, api_key=Secret("env:LINEAGE_TOKEN"))`, and `credentials=` on
`from_query`, `from_frame`, `from_files` and `sink_from`, whose function
reads the value with `Secret(name).value()`. An Iceberg catalog takes
`load_catalog("lake", **Storage({"token": Secret("bao:kv/rest#token")}).options())`.
Sverify reads a value when a table is opened and keeps none: `repr`,
reports, contract records, exports, logs and errors show the name.
[A test](../python/tests/test_secret_leaks.py) plants sentinel values in
every source and sink type and greps every output for them. Answers from
OpenBao and the cloud secret managers are kept for a minute
(`cache_seconds`), so a refresh that opens many tables asks once.

Each refresh entry lists the credentials its node used, by name, for
reading or writing (`StageRefresh.credentials`, `"credentials"` in
`Refresh.to_json`), and `node.credentials()` lists them before any run.
`sverify check` prints them, warns with `[scope]` when a sink lies outside
what its credential may write (`Storage(writes=[...])` or the
configuration's `writes`), and with `[inline_credentials]` when options
hold values or a URI holds them in its userinfo (`s3://key:secret@bucket`).
Where nothing is declared, an AWS session in the options
(`AWS_ACCESS_KEY_ID` and `AWS_SECRET_ACCESS_KEY`, with `AWS_SESSION_TOKEN`
for an assumed role) reports its own scope when `boto3` is installed
(`sverify[secrets-aws]`): sverify asks STS who the session is and reads the
`GetObject` and `PutObject` grants of that role's or user's policies, once
per credential. A `Deny`, a condition, a `NotAction`, `NotResource` or
a pattern that is not a prefix leaves the scope unknown, as does a session that
cannot read its own policies. Session policies, permissions boundaries and
bucket policies are not in the identity's policies, so the scope is what they
grant: a session policy or boundary can narrow the session below it, and a
bucket policy can widen it, so neither `in_scope` value is a guarantee. Other stores (GCS, Azure, a vended catalog credential) report nothing
yet and need `reads=` and `writes=`.
Every URI sverify records, reports, exports or sends is written without
userinfo, query string or fragment: a sink's `location`, `started`,
`credentials[].location`, the ODCS `physicalName` and the OpenLineage
namespace.
A source's cursor (`Source.restore`) is stored in clear in the sink's
table, so it must not be a credential.

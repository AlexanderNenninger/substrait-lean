### Credentials by name, and the credentials each node uses

Pipelines name their credentials and hold no value (#774). A
`sverify.io.Secret` says where a secret lives: `env:NAME`, `file:/path`,
`bao:kv/path#field` (OpenBao, and `vault:` for Vault, with token or GitHub
Actions OIDC login), `aws-sm:`, `gcp-sm:`, `azure-kv:` and `keychain:`
(extras `secrets-aws`, `secrets-gcp`, `secrets-azure`, `secrets-keychain`),
or a bare name that `[tool.sverify.secrets]` in `pyproject.toml` (or the file
`SVERIFY_SECRETS` names) maps. `Storage(credentials=...)`, `Secret` option
values, `FlightSource(secret=...)`, `Lineage(api_key=Secret(...))` and
`credentials=` on `from_query`, `from_frame`, `from_files` and `sink_from`
take them; `SecretError` names the secret, never its value (#775).
`FlightSource(token=)` is deprecated.

`node.credentials()`, each refresh entry (`StageRefresh.credentials`, and
`"credentials"` in the refresh JSON) and `sverify check` list the
credentials each node uses, by name, for reading or writing. `Storage(reads=,
writes=)` or the configuration declare a credential's scope, and `sverify
check` warns about a table outside it (`[scope]`) and about options given as
values (`[inline_credentials]`) (#778). A test plants sentinel secrets in
every source and sink type and greps every output for them (#777).

A Delta source's refresh reads the table's log twice where it read it four
times: the table `latest()` opened serves the change and the file listing
of that version (on S3, 383 requests per refresh became 309 in the
benchmark of the PR).

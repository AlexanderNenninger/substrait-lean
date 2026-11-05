# For enterprise

Your store, your credentials: the tables go to your bucket, and the
workflows reach it through OIDC with short-lived credentials, so no
long-lived key sits in GitHub. The workflows, the catalog and the data
branch's role stay the same: the `data` branch keeps only the catalog
sites.

Two repository variables (Settings, Secrets and variables, Actions,
Variables) switch the store:

| Variable | Value |
|---|---|
| `SVERIFY_STORE` | `s3`, `r2`, `gcs`, `azure` or `minio` (default `repository`) |
| `SVERIFY_BUCKET` | the lake's root: `s3://my-lake/pipelines`, `gs://…`, `az://<container>/pipelines` |

Tables go to `<bucket>/production/<table>` and `<bucket>/staging/pr-<n>/<table>`.

## Stages

Create two GitHub environments (Settings, Environments): `staging` and
`production`. Each gets its own variables below, so each stage's identity
is a different role:

- `staging`'s role writes only `<bucket>/staging/*`;
- `production`'s role writes `<bucket>/production/*` and reads nothing
  else. Restrict `production` to the `main` branch (Deployment branches)
  and add required reviewers if each refresh needs an approval.

GitHub's OIDC token names the environment in its subject,
`repo:<owner>/<repository>:environment:<name>`, so each role trusts only
its environment ([GitHub's OIDC docs](https://docs.github.com/en/actions/security-for-github-actions/security-hardening-your-deployments/about-security-hardening-with-openid-connect)).

## AWS S3

1. In IAM, add the identity provider `token.actions.githubusercontent.com`
   with the audience `sts.amazonaws.com`.
2. Create a role per environment. Trust policy condition:
   `token.actions.githubusercontent.com:sub` equals
   `repo:<owner>/<repository>:environment:staging` (or `production`).
   Permissions: `s3:ListBucket` on the bucket with an `s3:prefix` condition,
   and `s3:GetObject`, `s3:PutObject`, `s3:DeleteObject` on
   `arn:aws:s3:::my-lake/pipelines/staging/*` (or `production/*`).
3. Environment variables: `SVERIFY_AWS_ROLE` (the role's ARN) and
   `AWS_REGION`.

## Google Cloud Storage

1. Create a workload identity pool with a GitHub provider (issuer
   `https://token.actions.githubusercontent.com`, attribute mapping
   `google.subject=assertion.sub`).
2. A service account per environment, with `roles/storage.objectAdmin` on
   the bucket under an IAM condition on the object name prefix, and
   `roles/iam.workloadIdentityUser` for
   `principal://iam.googleapis.com/<pool>/subject/repo:<owner>/<repository>:environment:<name>`.
3. Environment variables: `SVERIFY_GCP_PROVIDER` (the provider's full
   name) and `SVERIFY_GCP_SERVICE_ACCOUNT`.

## Azure Blob Storage

1. An app registration (or a user-assigned managed identity) per
   environment, with a federated credential for the subject
   `repo:<owner>/<repository>:environment:<name>`.
2. The role Storage Blob Data Contributor on the container, with an ABAC
   condition on the path prefix.
3. Environment variables: `AZURE_CLIENT_ID`, `AZURE_TENANT_ID` and
   `AZURE_STORAGE_ACCOUNT_NAME`. `SVERIFY_BUCKET` is
   `az://<container>/pipelines`.

## Cloudflare R2

R2 has no OIDC federation: create an R2 API token per environment, scoped
to the bucket, and store it as the environment's secrets
`AWS_ACCESS_KEY_ID` and `AWS_SECRET_ACCESS_KEY`. Environment variable
`AWS_ENDPOINT_URL`: `https://<account id>.r2.cloudflarestorage.com`.
`SVERIFY_BUCKET` is `s3://<bucket>/pipelines`.

## MinIO over Tailscale, with OpenBao

The runner joins your tailnet, logs in to OpenBao with the Actions OIDC
token and gets MinIO credentials for its stage. No port opens to the
internet, and GitHub stores no MinIO key.

1. Tailscale: an OAuth client with the `auth_keys` scope, stored as the
   repository secrets `TS_OAUTH_CLIENT_ID` and `TS_OAUTH_SECRET`, and a tag
   for the runners (`tag:pipelines`, variable `TS_TAGS`). The runner joins
   as an ephemeral node; let the tag's ACL reach only MinIO and OpenBao
   ([tailscale/github-action](https://github.com/tailscale/github-action)).
2. OpenBao: enable JWT auth for GitHub, with a role per environment bound
   to its subject:

   ```bash
   bao auth enable jwt
   bao write auth/jwt/config \
     oidc_discovery_url=https://token.actions.githubusercontent.com \
     bound_issuer=https://token.actions.githubusercontent.com
   bao write auth/jwt/role/pipelines-production role_type=jwt \
     user_claim=sub bound_audiences=openbao \
     bound_claims='{"sub":"repo:<owner>/<repository>:environment:production"}' \
     policies=pipelines-production ttl=15m
   ```

   The policy reads the stage's MinIO keys (a KV entry, or a secrets
   engine that mints them).
3. Environment variables: `OPENBAO_ADDR` (its tailnet address),
   `OPENBAO_ROLE` (`pipelines-production`), `OPENBAO_SECRETS` in
   [vault-action's format](https://github.com/hashicorp/vault-action), such
   as `kv/data/pipelines/production access_key | AWS_ACCESS_KEY_ID ;
   kv/data/pipelines/production secret_key | AWS_SECRET_ACCESS_KEY`, and
   `AWS_ENDPOINT_URL`, MinIO's tailnet address
   (`http://minio.<tailnet>.ts.net:9000`).
4. MinIO: a user or policy per stage limited to its prefix.

Vault works the same way as OpenBao (same API), and so does a cloud secret
manager with OIDC login. Another zero-trust network or VPN takes
Tailscale's place if its client can join from a runner.

## The catalog

GitHub Pages publishes the catalog, and Pages sites can be public even for
a private repository. For enterprise the pages show the contract, the
lineage, the freshness and the chart, and carry no rows. Set the
variable `SVERIFY_CATALOG_DATA` to `snapshot` to add a copy of each table
for the query box, or to `none` with everything in your repository to
leave the data out there too.

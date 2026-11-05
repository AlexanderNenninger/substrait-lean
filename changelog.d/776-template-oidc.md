### The pipeline template keeps stored keys to the store that needs them

The template's `lake.yml` passes a stored key to a job only when the store
has no OIDC federation (R2), and the Tailscale client's secret only for
MinIO; S3, GCS and Azure log in through OIDC with nothing stored (#776).
`docs/for-enterprise.md` gives each environment's role read grants on the
sources and write grants on its stage only (#778), and says how a source
token reaches a pipeline by name.

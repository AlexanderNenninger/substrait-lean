### The report says which build of the checker proved it

A checker built without `check_generated` (a plain `lake build`, an editable
install, `SVERIFY_CHECKER`, a borrowed binary) holds its generated lift and
lowering proofs as `sorry`. The report's JSON gains `checker.generated_proofs`
(`true`, `false`, or `null` where the checker does not say), and `str(report)`
starts with "proved by a checker whose generated proofs are unchecked" for such
a build. The proof cache keys on it (#1484, [trusted base](docs/trusted-base.md)).

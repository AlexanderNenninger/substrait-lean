### A stale checker fails with a clear message

`substrait-check --version` prints the checker's protocol, and sverify checks
it once per process: a checker older or newer than the package raises
`sverify.errors.CheckerVersionError`, which says how to rebuild it (`uv sync`
or `lake build substrait-check`), where a stale build used to fail later with a
`KeyError`.

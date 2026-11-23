### Breaking: exit codes run from the best to the worst (#2458)

`sverify check`, `refresh` and `explain` (and the `exit` of their JSON) number
their exit codes by severity, so the worst of several runs is their maximum.
`sverify.cli.ExitCode` names them, and `sverify-dbt` and the pipeline
template's `lake.py` read it.

| Outcome | 0.8.0 | Now |
|---|---|---|
| proved | 0 | 0 |
| not proved | 1 | 1 |
| usage | 2 | 2 |
| unsupported | 3 | 3 |
| refused (no route to the engine) | 3 (with unsupported) | 4 |
| budget exceeded | 4 | 5 |
| quarantined | 5 | 6 |
| held | 5 (with quarantined) | 7 |
| error | 6 | 8 |

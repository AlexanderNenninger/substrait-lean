### One verb for proving, and the plan layer in a module of its own

Breaking.

- `ContractedTransform.check(...)` is `ContractedTransform.verify(...)`: "verify"
  proves (`sv.verify`, `.verify`), and "check" reads data (`check_requires`,
  `Report.check_inputs`, `proved_with_checks`). The commands keep their names:
  `sverify check` and `sverify-dbt check` verify a project.
- `on_unproved="runtime"` is refused; write `on_unproved="check"`.
- The plan layer moved to `sverify.engines.plan`, outside the 1.x promise:
  `to_sql`, `substrait_json`, `written_plan` and `delta_plans`. Import them
  from there; `sverify.engines` no longer has them. `sverify.engines.create_table`
  and `table_rows` are gone (`con.create`, `con.rows`), and so is
  `sverify.engines.Unsupported` (`UnsupportedError`).
- `sverify.errors` says which exceptions keep a built-in base, and the bases
  are fixed for 1.x.
- `sverify check --fix` and `--diff` say that the preconditions they write
  narrow the input each node accepts.

([#881](https://github.com/AlexanderNenninger/substrait-lean/issues/881))

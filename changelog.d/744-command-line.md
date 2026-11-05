### The `sverify` command

- `sverify check <file>[:<node>]` proves every contracted transform and node
  a Python file applies, without running it, and prints the contract in
  plain words first: what the output guarantees, what each refresh checks
  on the data, and what is not proved, each finding with a code. A dbt
  project goes to `sverify-dbt check`
  ([#744](https://github.com/AlexanderNenninger/substrait-lean/issues/744)).
- `check --full` adds each node's full report; `check --diff` shows the
  preconditions the proofs need (`Report.needs`) as a diff of the
  decorators' `requires=`, and `check --fix` writes them and checks again.
- `sverify suggest` from #786 is now `check --fix` and `check --diff`, and
  `sverify explain <file>:<node>` is `check --full`; `explain` takes codes
  only (API review I2, I3). Neither was released, so no aliases remain.
- `sverify refresh <file>:<node>` runs a node and reports what changed;
  `sverify explain <code>` says what a code means and how to fix it. The
  codes are snake case, as the report writes them.
- `--format text|json|github|sarif|junit` (`--output-format`; `--json` is
  `--format json`). The JSON is format 1 of `schemas/cli.schema.json`, with
  each node's `Report.to_json()`. `github` annotates a pull request's lines,
  `sarif` is SARIF 2.1.0 for code scanning, `junit` a test report
  ([#793](https://github.com/AlexanderNenninger/substrait-lean/issues/793)).
- Exit codes: 0 proved, 1 not proved, 2 usage error, 3 unsupported or
  refused, 4 time or memory budget exceeded, 5 a refresh quarantined rows or
  held a node, 6 error.
- `--timeout` (default 30 s, `SVERIFY_TIMEOUT`, 0 turns it off) bounds
  proof, planning and checking, never a refresh moving data.
  `--memory-limit` (`SVERIFY_MEMORY_LIMIT`) sets DuckDB's `memory_limit`,
  with a spill directory (`SVERIFY_SPILL_DIRECTORY`); a breach stops before
  any sink commits.
- `sverify.cli.discover(path)` does what `check` does from Python.

### The `sverify` command

- `sverify check <file>[:<node>]` proves every contracted transform and node
  a Python file applies, without running it, and prints the contract in
  plain words first: what the output guarantees, what each refresh checks
  on the data, and what is not proved, each problem with a code. A dbt
  project goes to `sverify-dbt check`
  ([#744](https://github.com/AlexanderNenninger/substrait-lean/issues/744)).
- `sverify suggest <file> [--apply]` writes the preconditions the proofs
  need (`Report.needs`) into the decorators' `requires=`, then checks the
  file again.
- `sverify refresh <file>:<node>` runs a node and reports what changed;
  `sverify explain <code>` explains a code, and `sverify explain
  <file>:<node>` prints a node's full report.
- Every command takes `--json` (a provisional format until #736) and exits
  0 proved, 1 not proved, 2 refused, 3 budget exceeded, 4 error.
- `--timeout` (default 30 s, `SVERIFY_TIMEOUT`, 0 turns it off) bounds
  proof, planning and checking, never a refresh moving data.
  `--memory-limit` (`SVERIFY_MEMORY_LIMIT`) sets DuckDB's `memory_limit`,
  with a spill directory (`SVERIFY_TEMP_DIRECTORY`); a breach stops before
  any sink commits.
- `sverify.cli.discover(path)` does what `check` does from Python.

### Breaking: the `sverify` command before 1.0 (API review I1–I5)

The command 0.6.0 shipped (#744) changes its exit codes, flags and JSON
before 1.x freezes them
([#797](https://github.com/AlexanderNenninger/substrait-lean/pull/797)):

- Exit codes: 0 proved (a refresh committed every row), 1 not proved,
  2 usage error (argparse's too), 3 unsupported or refused, 4 time or
  memory budget exceeded, 5 a refresh quarantined rows or held a node,
  6 error. In 0.6.0, 2 was refused, 3 budget, 4 error. `sverify --help`
  lists them.
- `sverify suggest <file> [--apply]` is `sverify check <file> --diff` (show)
  and `--fix` (write, then check again).
- `sverify explain <file>:<node>` is `sverify check <file>:<node> --full`;
  `explain` takes codes only.
- Codes are snake case (`may_be_false`), as the report writes them, each with
  a level; `explain` still reads kebab case.
- `--format text|json|github|sarif|junit` (`--output-format`; `--json` is
  `--format json`). `github` writes workflow commands that annotate a pull
  request's lines, `sarif` a SARIF 2.1.0 log for code scanning, `junit` a
  test report
  ([#793](https://github.com/AlexanderNenninger/substrait-lean/issues/793)).
- The JSON is format 1 of `schemas/cli.schema.json`: each node's `name`,
  `nodes`, `status`, `summary` (its third key is `not_proved`), `links` and
  `report`, the node's `Report.to_json()`. The 0.6.0 keys `verdict`,
  `problems`, `needs` and `facts` come from the embedded report.
- `sverify contract export` (#791) follows the same exit codes.
- `import sverify` loads its names on first use: `sverify --help`,
  `--version` and `explain` take 0.1 s, down from 1.3 s.

### `sverify check --format junit` is removed

0.7.0's `junit` output is gone before 1.x freezes the command: JUnit XML has
no schema, only the conventions of each CI system that reads it. Use
`--format sarif` for code scanning, `--format github` for annotations on a
pull request, or `--format json` (`schemas/cli.schema.json`) for anything
else.

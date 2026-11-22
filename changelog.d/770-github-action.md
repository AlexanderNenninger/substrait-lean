### A GitHub Action for `sverify check`

`actions/check/` is a composite action that installs `sverify`, runs `sverify check --format sarif` on each target with the default 30 s timeout, merges the logs into one SARIF run and uploads it to code scanning (part of [#770](https://github.com/AlexanderNenninger/substrait-lean/issues/770), item 1). Its job exits with the worst code of the targets', and an `action` workflow tests it on two example pipelines, one proved and one not. [Checking without running](../docs/how-to-command-line.md#in-github-actions) says how to use it.

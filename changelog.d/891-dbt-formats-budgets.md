### `sverify-dbt check` prints for CI and takes sverify's budgets

`sverify-dbt check --format github|sarif|junit` prints one annotation per finding on the model's file, a SARIF 2.1.0 log, or a JUnit suite per model. `--timeout` and `--memory-limit` bound the check as they do in `sverify check`, which now passes both through for a dbt project; a check past either exits 5. The time limit is off unless `--timeout` or `$SVERIFY_TIMEOUT` sets it: a project check is many models, and `sverify check`'s 30 s is per file (#891).

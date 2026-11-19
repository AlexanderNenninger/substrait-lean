### `sverify-dbt check` prints for CI and takes sverify's budgets

`sverify-dbt check --format github|sarif|junit` prints one annotation per finding on the model's file, a SARIF 2.1.0 log, or a JUnit suite per model. `--timeout` and `--memory-limit` bound the check as they do in `sverify check`, which now passes both through for a dbt project; a check past either exits 4 (#891).

### `sverify check <dbt dir> --format json` works

`sverify-dbt check` takes `--format text|json` (`--json` stays as the alias), the flag `sverify check` forwards to it. For a dbt project `sverify check` prints text or JSON; `--format github`, `sarif` and `junit` stop with a usage error instead of reaching sverify-dbt's parser (#891).

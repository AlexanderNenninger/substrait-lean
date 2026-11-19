### `sverify-dbt check --selectors` needs the whole project

`--selectors` with `--select` stops with a usage error, and `CheckResult.write_selectors` raises `ValueError` after a partial check: the selector would have replaced the proved tests of every model outside the selection, and `dbt build --exclude selector:sverify_proved` would have run them all again without a word (#891, 1.6).

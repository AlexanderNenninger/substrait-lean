### sverify-dbt lives in this repository and is released with sverify

`sverify-dbt` ([`dbt/`](dbt/README.md)), which proves a DuckDB dbt
project's data tests and model contracts before the models run, is back in
this repository with its history. From this release on it is published to
PyPI with sverify, at the same version, pinning `sverify==<version>`. The
`dbt` CI job runs its tests, its check of the sample project
(`dbt/examples/shop`, 19 of 26 tests and constraints proved), and
`dbt build` without the proved tests
([#732](https://github.com/AlexanderNenninger/substrait-lean/issues/732),
[#177](https://github.com/AlexanderNenninger/substrait-lean/issues/177)).

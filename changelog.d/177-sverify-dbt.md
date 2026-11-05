### sverify-dbt checks a dbt project's tests and contracts

`sverify-dbt`, a package of its own in [`dbt/`](dbt/README.md), proves a
DuckDB dbt project's data tests and model contracts after `dbt compile`.
Each model's compiled SQL is checked against the tests on the models and
sources it reads. `sverify-dbt check <project>` lists per model the tests
proved before it runs, the tests not proved with a counterexample, the
models refused with the reason, and the source tests a model needs, and
`--selectors` writes a selector so that `dbt build` skips the proved tests.
The sample project in `dbt/examples/shop` runs in CI
([#177](https://github.com/AlexanderNenninger/substrait-lean/issues/177)).

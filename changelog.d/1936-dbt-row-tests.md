### sverify-dbt reads more row-level tests

`sverify-dbt` maps the regex, LIKE, length and column-pair tests of dbt-expectations, and `not_accepted_values` and `not_empty_string` of dbt-utils, to conditions sverify proves ([#1936](https://github.com/AlexanderNenninger/substrait-lean/issues/1936)). A regex test with `flags` is listed as not checked, with the reason.
